(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Sign
open Pos
open Files
open Syntax
open Sig_state
open Scope
open Print

(** Logging function for command handling. *)
let log_hndl = new_logger 'h' "hndl" "command handling"
let log_hndl = log_hndl.logger

(* Register a check for the type of the builtin symbols "0" and "+1". *)
let _ =
  let register = Builtin.register_expected_type (Unif.eq_noexn []) pp_term in
  let expected_zero_type ss _pos =
    try
      match !((StrMap.find "+1" ss.builtins).sym_type) with
      | Prod(a,_) -> a
      | _ -> assert false
    with Not_found -> Meta (fresh_meta Type 0, [||])
  in
  register "0" expected_zero_type;
  let expected_succ_type ss _pos =
    let typ_0 =
      try lift !((StrMap.find "0" ss.builtins).sym_type)
      with Not_found -> _Meta (fresh_meta Type 0) [||]
    in
    Bindlib.unbox (_Impl typ_0 typ_0)
  in
  register "+1" expected_succ_type

(** Representation of a yet unchecked proof. The structure is initialized when
    the proof mode is entered, and its finalizer is called when the proof mode
    is exited (i.e., when a terminator like “end” is used).  Note that tactics
    do not work on this structure directly,  although they act on the contents
    of its [pdata_p_state] field. *)
type proof_data =
  { pdata_stmt_pos : Pos.popt (* Position of the proof's statement.  *)
  ; pdata_p_state  : Proof.t  (* Initial proof state for the proof.  *)
  ; pdata_tactics  : p_tactic list (* Tactics for the proof.         *)
  ; pdata_finalize : sig_state -> Proof.t -> sig_state (* Finalizer. *)
  ; pdata_end_pos : Pos.popt (* Position of the proof's terminator. *)
  ; pdata_expo     : Terms.expo (* Allow use of private symbols      *) }

(** [handle_open pos ss p] handles the command [open p] with [ss] as the
   signature state. On success, an updated signature state is returned. *)
let handle_open : popt -> sig_state -> Path.t -> sig_state =
    fun pos ss p ->
  (* Obtain the signature corresponding to [m]. *)
  let sign =
    try PathMap.find p !(Sign.loaded) with Not_found ->
      (* The signature has not been required... *)
      fatal pos "Module [%a] has not been required." Path.pp p
  in
  (* Open the module. *)
  open_sign ss sign

(** [handle_require b pos ss p] handles the command [require p] (or [require
   open p] if b is true) with [ss] as the signature state. On success, an
   updated signature state is returned. *)
let handle_require : bool -> popt -> sig_state -> Path.t -> sig_state =
    fun b pos ss p ->
  (* Check that the module has not already been required. *)
  if PathMap.mem p !(ss.signature.sign_deps) then
    fatal pos "Module [%a] is already required." Path.pp p;
  (* Add the dependency (it was compiled already while parsing). *)
  ss.signature.sign_deps := PathMap.add p [] !(ss.signature.sign_deps);
  if b then handle_open pos ss p else ss

(** [handle_modifiers ms] verifies that the modifiers in [ms] are compatible.
    If so, they are returned as a tuple, otherwise, the incompatible modifiers
    are returned. *)
let handle_modifiers : p_modifier loc list -> (prop * expo * match_strat) =
  fun ms ->
  let is_expo {elt; _} = match elt with P_expo(_) -> true | _ -> false in
  let is_prop {elt; _} = match elt with P_prop(_) -> true | _ -> false in
  let is_mstrat {elt; _} = match elt with P_mstrat(_) -> true | _ -> false in
  let die (mods: p_modifier loc list) =
    let pp_sep oc () = Format.pp_print_string oc "; " in
    let pp_pmloc oc (m: p_modifier loc) =
      Format.fprintf oc "%a:\"%a\"" Pos.print_short m.pos Pretty.pp_modifier m
    in
    fatal_no_pos "%a" (Format.pp_print_list ~pp_sep pp_pmloc) mods
  in
  let prop = List.filter is_prop ms in
  let prop =
    match prop with
    | _::_::_ ->
        fatal_msg "Only one property modifier can be used, \
                   %d have been found: " (List.length prop);
        die prop
    | [{elt=P_prop(p); _}] -> p
    | [] -> Defin
    | _ -> assert false
  in
  let expo = List.filter is_expo ms in
  let expo =
    match expo with
    | _::_::_ ->
        fatal_msg "Only one exposition marker can be used, \
                   %d have been found: " (List.length expo);
        die expo
    | [{elt=P_expo(e); _}] -> e
    | [] -> Public
    | _ -> assert false
  in
  let mstrat = List.filter is_mstrat ms in
  let mstrat =
    match mstrat with
    | _::_::_ ->
        fatal_msg "Only one strategy modifier can be used, \
                   %d have been found: " (List.length mstrat);
        die mstrat
    | [{elt=P_mstrat(s); _ }] -> s
    | [] -> Eager
    | _ -> assert false
  in
  (prop, expo, mstrat)

(** [handle_require_as pos ss p id] handles the command [require p as id] with
   [ss] as the signature state. On success, an updated signature state is
   returned. *)
let handle_require_as : popt -> sig_state -> Path.t -> ident -> sig_state =
  fun pos ss p id ->
  let ss = handle_require false pos ss p in
  let aliases = StrMap.add id.elt p ss.aliases in
  let path_map = PathMap.add p id.elt ss.path_map in
  {ss with aliases; path_map}

(** [data_proof] returns the datas needed for the symbol or definition
    [sig_symbol] to be added in the signature and the [goals] we wish to prove
    with the proof script [ts pe]. [pdata_expo] sets the authorized exposition
    of the symbols used in the proof script : Public (= only public symbols)
    or Privat (= public and private symbols) *)
let data_proof : sig_symbol -> expo -> p_tactic list ->
  p_proof_end loc -> Proof.Goal.t list -> proof_data =
  fun sig_symbol pdata_expo ts pe goals ->
  let ident = sig_symbol.ident in
  let typ   = sig_symbol.typ   in
  let def   = sig_symbol.def   in
  let pos = ident.pos in
  (* Initialize proof state and save configuration data. *)
  let proof_term = fresh_meta ~name:ident.elt typ 0 in
  let ps = Proof.{proof_name = ident ; proof_term ; proof_goals = goals} in
  Console.push_state ();
  (* Build proof checking data. *)
  let finalize ss ps =
    Console.pop_state ();
    match pe.elt with
    | P_proof_abort ->
      (* Just ignore the command, with a warning. *)
      wrn pos "Proof aborted."; ss
    | _ ->
      let ps = Tactics.solve ps pos in
      (* We check that no metavariable remains. *)
      if Basics.has_metas true typ then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n"
            ident.elt;
          fatal ident.pos "We have %s : %a." ident.elt pp_term typ
        end;
      begin
        match def with
        | Some(t) ->
          if Basics.has_metas true t then
            begin
              fatal_msg
                "The definition of [%s] has unsolved metavariables.\n"
                ident.elt;
              fatal ident.pos "We have %s : %a ≔ %a."
                ident.elt pp_term typ pp_term t
            end;
        | None -> ()
      end;
      match pe.elt with
      | P_proof_abort -> assert false (* Handled above *)
      | P_proof_admit ->
        (* If the proof is finished, display a warning. *)
        if Proof.finished ps then
          wrn pos "The proof is finished. You can use 'end' instead.";
        (* Add a symbol corresponding to the proof, with a warning. *)
        out 3 "(symb) %s (admit)\n" ident.elt;
        wrn pos "Proof admitted.";
        add_symbol ss sig_symbol
      | P_proof_end   ->
        (* Check that the proof is indeed finished. *)
        if not (Proof.finished ps) then
          begin
            let _ =
              Tactics.handle_tactic ss pdata_expo ps (none P_tac_print)
            in
            fatal pos "The proof is not finished."
          end;
        (* Add a symbol corresponding to the proof. *)
        out 3 "(symb) %s (end)\n" ident.elt;
        add_symbol ss sig_symbol
  in
  let data =
    { pdata_stmt_pos = pos ; pdata_p_state = ps ; pdata_tactics = ts
    ; pdata_finalize = finalize ; pdata_end_pos = pe.pos
    ; pdata_expo = pdata_expo }
  in
  data

(** [handle_cmd ss cmd] tries to handle the command [cmd] with [ss] as the
    signature state. On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
  fun ss cmd ->
  let scope_basic exp p_t =
    let t,m = Scope.scope_term exp ss Env.empty p_t in
    t,m
  in
  match cmd.elt with
  | P_require(b,ps)            ->
    let ps = List.map (List.map fst) ps in
    (List.fold_left (handle_require b cmd.pos) ss ps, None)
  | P_require_as(p,id)         ->
    let id = Pos.make id.pos (fst id.elt) in
    (handle_require_as cmd.pos ss (List.map fst p) id, None)
  | P_open(ps)                  ->
    let ps = List.map (List.map fst) ps in
    (List.fold_left (handle_open cmd.pos) ss ps, None)
  | P_symbol(ms, st, t, ts_pe, e) ->
    let x,xs,ao = st.elt in
    (*   : U  := V begin..end *)
    begin
      match (ao, e, t, ts_pe) with
      | (   None, Def, None  , Some _) ->
        fatal x.pos ":= proofterm via proofscript but without type"
      | (      _, Def, None  , None  ) ->
        fatal x.pos ":= without definition term nor proofscript"
      | _ -> ()
    end;
    let is_opaq {elt; _} =
      match elt with
      | P_opaq(Opaque) -> true
      | _ -> false
    in
    let op = List.exists is_opaq ms in
    (* Verify modifiers. *)
    let (prop, expo, mstrat) = handle_modifiers ms in
    (* We check that [x] is not already used. *)
    if Sign.mem ss.signature x.elt then
      fatal x.pos "Symbol [%s] already exists." x.elt;
    let data =
      (* Desugaring of arguments and scoping of [t]. *)
      let p_t,t,metas_t =
        match t with
        | Some t ->
          let p_t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
          let t,meta_t = scope_basic expo p_t in
          Some p_t, Some t, meta_t
        | None -> None, None, MetaSet.empty
      in
      (* Desugaring of arguments and argument impliciteness. *)
      let (ao, impl) =
        match ao with
        | None    -> (None, List.map (fun (_,_,impl) -> impl) xs)
        | Some(a) ->
          let a = if xs = [] then a else Pos.none (P_Prod(xs,a)) in
          (Some(a), Scope.get_implicitness a)
      in
      let ao,metas_a =
        begin
          match ao with
          | Some ao -> let a,m = scope_basic expo ao in Some a, m
          | None -> None, MetaSet.empty
        end
      in
      (* If a type [ao = Some a] is given, then we check that it is
         typable by a sort and that [t] has type [a]. Otherwise, we
             try to infer thetype of [t]. Unification goals are collected *)
      (* Proof script *)
      let (ts,pe) =
        let p_end = Pos.make cmd.pos P_proof_end in
        let _solve = Pos.make cmd.pos P_unif_solve in
        begin
          match p_t,ts_pe with
          | Some p_t,None ->
            [Pos.make cmd.pos (P_tac_refine(p_t))], p_end
          | Some p_t,Some(ts,pe) ->
            Pos.make cmd.pos (P_tac_refine(p_t))::ts, pe
          | None,Some(ts,pe) -> ts,pe
          | None,None -> [],p_end
        end
      in
      let metas_t_a = MetaSet.union metas_t metas_a in
      let add_goal m = List.insert Proof.Goal.compare (Proof.Goal.goal_typ_of_meta m) in
      let typ_goals_from_metas = MetaSet.fold add_goal metas_t_a [] in
      let typ_goals_from_metas = List.map Proof.Goal.typ typ_goals_from_metas in
      let goals,sig_symbol,pdata_expo =
        let sort_goals, a = Proof.goals_of_typ x.pos ao t in
        (* And the main "type" goal *)
        let typ_goal =
          match e with
          | Def ->
            let proof_term = fresh_meta ~name:x.elt a 0 in
            let proof_goal = Proof.goal_of_meta proof_term in
            [proof_goal] @ typ_goals_from_metas
          | Tac ->
            typ_goals_from_metas
        in
        let goals = sort_goals @ typ_goal in
        let sig_symbol = {expo;prop;mstrat;ident=x;typ=a;impl;def=t} in
        (* Depending on opacity : theorem = false / definition = true *)
        let pdata_expo =
          match e, op,ao,prop,mstrat with
          (* Theorem *)
          |   Tac,     _,      _ ,    _ ,     _  -> expo
          |     _, true ,      _ , Defin, Eager  -> Privat
          |     _, true ,      _ , _    , Eager  ->
            fatal cmd.pos "Property modifiers can't be used in \
                           theorems."
          |     _, true ,      _ , _    , _      ->
            fatal cmd.pos "Pattern matching strategy modifiers cannot \
                           be used in theorems."
(*
                |     _, true , None   , _    , _      ->
                  fatal cmd.pos "Theorem should have an explicit type !"
*)
          (* Definition *)
(*
                |     _, false, _      , Const, _      ->
                  fatal cmd.pos "A definition cannot be a constant."
*)
          |     _, false, _      , _    , Sequen ->
            fatal cmd.pos "Pattern matching strategy modifiers cannot \
                           be used in definitions."
          |     _, false, _      , _    , _      -> expo
        in
        goals,sig_symbol,pdata_expo
      in
      data_proof sig_symbol pdata_expo ts pe goals
    in
    (ss, Some(data))
  | P_rules(rs)                ->
      (* Scoping and checking each rule in turn. *)
      let handle_rule r =
        let pr = scope_rule ss r in
        let sym = pr.elt.pr_sym in
        if !(sym.sym_def) <> None then
          fatal pr.pos "Rewriting rules cannot be given for defined \
                        symbol [%s]." sym.sym_name;
        (sym, Pos.make r.pos (Sr.check_rule pr))
      in
      let rs = List.map handle_rule rs in
      (* Adding the rules all at once. *)
      let add_rule (s,r) =
        Sign.add_rule ss.signature s r.elt;
        out 3 "(rule) %a\n" pp_rule (s,r.elt)
      in
      List.iter add_rule rs;
      let syms = List.remove_phys_dups (List.map (fun (s, _) -> s) rs) in
      List.iter Tree.update_dtree syms;
      (ss, None)
  | P_set(cfg)                 ->
      let ss =
        let with_path : Path.t -> qident -> qident = fun path qid ->
          let path = List.map (fun s -> (s, false)) path in
          Pos.make qid.pos (path, snd qid.elt)
        in
        match cfg with
        | P_config_builtin(s,qid) ->
            (* Set the builtin symbol [s]. *)
            if StrMap.mem s ss.builtins then
              fatal cmd.pos "Builtin [%s] already exists." s;
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            Builtin.check ss cmd.pos s sym;
            out 3 "(conf) set builtin \"%s\" ≔ %a\n" s pp_symbol sym;
            Sig_state.add_builtin ss s sym
        | P_config_unop(unop)     ->
            let (s, prio, qid) = unop in
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            (* Make sure the operator has a fully qualified [qid]. *)
            let unop = (s, prio, with_path sym.sym_path qid) in
            out 3 "(conf) %a %a\n" pp_symbol sym pp_hint (Prefix unop);
            Sig_state.add_unop ss s (sym, unop)
        | P_config_binop(binop)   ->
            let (s, assoc, prio, qid) = binop in
            (* Define the binary operator [sym]. *)
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            (* Make sure the operator has a fully qualified [qid]. *)
            let binop = (s, assoc, prio, with_path sym.sym_path qid) in
            out 3 "(conf) %a %a\n" pp_symbol sym pp_hint (Infix binop);
            Sig_state.add_binop ss s (sym, binop);
        | P_config_ident(id)      ->
            Sign.add_ident ss.signature id;
            out 3 "(conf) declared identifier \"%s\"\n" id; ss
        | P_config_quant(qid)     ->
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            out 3 "(conf) %a quantifier\n" pp_symbol sym;
            Sig_state.add_quant ss sym
        | P_config_unif_rule(h)   ->
            (* Approximately same processing as rules without SR checking. *)
            let pur = (scope_rule ss h).elt in
            let urule =
              { lhs = pur.pr_lhs
              ; rhs = Bindlib.(unbox (bind_mvar pur.pr_vars pur.pr_rhs))
              ; arity = List.length pur.pr_lhs
              ; arities = pur.pr_arities
              ; vars = pur.pr_vars
              ; xvars_nb = pur.pr_xvars_nb }
            in
            Sign.add_rule ss.signature Unif_rule.equiv urule;
            Tree.update_dtree Unif_rule.equiv;
            out 3 "(hint) [%a]\n" Print.pp_rule (Unif_rule.equiv, urule); ss
      in
      (ss, None)
  | P_query(q)                 ->
      Queries.handle_query ss None q; (ss, None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [handle_cmd ss cmd] adds to the previous [handle_cmd] some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
  fun ss cmd ->
  Print.sig_state := ss;
  try
    let (tm, ss) = time (handle_cmd ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           ->
      fatal cmd.pos "Uncaught exception [%s]." (Printexc.to_string e)
