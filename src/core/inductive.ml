(** Generating of induction principles. *)

open! Lplib

open Timed
open Pos
open Console
open Terms
open Print
open Syntax

(** Logging function for generating of inductive principle. *)
let log_ind = new_logger 'g' "indu" "generating induction principle"
let log_ind = log_ind.logger

(** Builtin configuration for induction. *)
type config =
  { symb_Prop : sym (** : TYPE. Type of propositions. *)
  ; symb_prf  : sym (** : Prop → TYPE.
                        Interpretation of propositions as types. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_Prop = builtin "Prop"
  ; symb_prf  = builtin "P" }

(** [check_typ_ind rec_typ] checks if the type of the term [rec_typ] is the
    constant TYPE. *)
let check_type_ind : popt -> term -> unit = fun pos rec_typ ->
  match Typing.infer [] rec_typ with
  | Some t ->
      begin
      match unfold t with
      | Type   -> ()
      | _ -> fatal pos "The type of the generated inductive principle of [%a]
                        isn't the constant TYPE. Please, raise an issue."
               pp_term rec_typ
      end
  | None   ->
      fatal pos "The type of the generated inductive principle of
                 [%a] isn't typable. Please, raise an issue."
        pp_term rec_typ

(** [gen_ind_typ_codom pos ind_sym codom s] assumes that the type of [ind_sym]
    is of the form [Π(i1:a1),...,Π(in:an), TYPE]. It then generates a [tbox]
    similar to this type except that [TYPE] is replaced by
    [codom [i1;...;in]]. The string [s] is the prefix of variables' name. *)
let gen_ind_typ_codom : popt -> sym -> (tbox list -> tbox) -> string -> tbox =
  fun pos ind_sym codom s ->
  let rec aux : tvar list -> term -> tbox = fun xs a ->
    match Basics.get_args a with
    | (Type, _) -> codom (List.rev_map _Vari xs)
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b s in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ -> fatal pos "The type of %a is not supported" pp_symbol ind_sym
  in aux [] !(ind_sym.sym_type)

(** [fold_cons_typ pos codom inj_var build_rec_hyp domrec dom ind_sym cons_sym
    f_rec f_not_rec init s] generates some value iteratively by going through
    the structure of [cons_sym.sym_type]. The argument [pos] is the position
    of the command inductive where the inductive type was defined. The symbol
    [ind_sym] is the type of the current inductive type, and the symbol
    [cons_sym] is the current constructor. If you would like to store a
    temporary result, the initial value is [init], and you can change this
    value in the recursive case with the function [f_rec res x rec_hyp], and
    on the other case with the function [f_not_rec res x]. The string [s] is
    the prefix of variables' name. It's useful for the function [inj_var] to
    have names with no clash.
    In this iteration, we keep track of the variables [xs] we went through
    (the last variable comes first) and some accumulor [acc:'a]. Note that, at
    the beginning, the function [fold_cons_typ] is equal to
    [aux [] init  !(cons_sym.sym_type)] where
    [aux : 'b list -> 'a -> term -> 'c = fun xs acc a].
    During an iteration, there are several cases:
      1) If the current type is of the form [ind_sym ts], then we call
         [codom ts xs acc].
      2) If the current type is a product of the form [Π(x:ind_sym ts), b],
         then we are in case of recursive occurrences, so the function
         [build_rec_hyp ts x] builds the recursive hypothesis associated, and
         then the function [domrec a x rec_hyp next] is applied to conclude
         the building ([rec_hyp] is the current recursive hypothesis and
         [next] is the result of the recursive call).
      3) If the current type is a product [Π(x:a), b] not of the previous
         form, then the function [dom a x next] is called.
      4) Any other case is an error.*)
let fold_cons_typ (pos : popt) (codom : term list -> 'b list -> 'a -> 'c)
      (inj_var : 'b list -> tvar -> 'b)
      (build_rec_hyp : term list -> 'b -> 'a)
      (domrec : term -> 'b -> 'a -> 'c -> 'c) (dom : term -> 'b -> 'c -> 'c)
      (ind_sym : sym) (cons_sym : sym) (f_rec : 'a -> 'b -> 'a -> 'a)
      (f_not_rec : 'a -> 'b -> 'a) (init : 'a) (s : string) : 'c =
  let rec aux : 'b list -> 'a -> term -> 'c = fun xs acc a ->
    match Basics.get_args a with
    | (Symb(s), ts) ->
       if s == ind_sym then codom ts xs acc
       else fatal pos "%a is not a constructor of %a"
              pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b s in
        let x = inj_var xs x in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
             if s == ind_sym then
               let rec_hyp = build_rec_hyp ts x in
               let next = aux (x::xs) (f_rec acc x rec_hyp) b in
               domrec a x rec_hyp next
             else
               let next = aux (x::xs) (f_not_rec acc x) b in
               dom a x next
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in aux [] init !(cons_sym.sym_type)

(** [gen_rec_type ss pos ind_sym cons_list] generates the induction principle
    of the inductive type [ind_sym] (and its position [pos]) with the cons-
    tructors [cons_list]. Each recursive argument is followed by its induction
    hypothesis. For instance, with [inductive T:TYPE := c: T->T->T], we have
    [ind_T: Πp:T->Prop, (Πx0:T, π(p x0)-> Πx1:T, π(p x1)-> π(p (c x0 x1)) ->
    Πx:T, π(p x)]. Indeed, if the user doesn't give a name for an argument
    (in case of no dependent product in fact), a fresh name will create (xi
    with a fresh i). In general, thanks to this function, the command
    inductive T : Π(i1:A1),...,Π(im:Am), TYPE := c1:T1 | ... | cn:Tn generates
    ind_T: Π(p:Π(i1:A1),...,Π(im:Am), T i1 ... im -> Prop), U1 -> ... -> Un ->
    (Π(i1:A1),...,Π(im:Am), Π(t:T i1 ... im), π(p i1 ... im t))
    where Ui is the clause associated to the constructor ci. *)
let gen_rec_type : Sig_state.t -> popt -> sym -> sym list -> term =
  fun ss pos ind_sym cons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let c = get_config ss pos in
  let set =
    let f set sym =
      let s = sym.sym_name in
      if s <> "" && (s.[0] = 'x' || s.[0] = 'p') then
        Extra.StrSet.add s set
      else set
    in
    List.fold_left f Extra.StrSet.empty (ind_sym::cons_list)
  in
  let x_str = Extra.get_safe_prefix "x" set in
  let p_str = Extra.get_safe_prefix "p" set in
  let p = Bindlib.new_var mkfree p_str in
  let app  : tbox -> tbox list -> tbox = List.fold_left _Appl in
  let fapp : sym  -> tbox list -> tbox = fun f ts -> app (_Symb f) ts in
  let prf_of_p : tbox list -> tbox -> tbox = fun ts t ->
    fapp c.symb_prf [_Appl (app (_Vari p) ts) t]
  in

  (* STEP 1: Create the type of the property p *)
  let prop = _Symb c.symb_Prop in
  let codom ts = _Impl (fapp ind_sym ts) prop in
  let p_type = gen_ind_typ_codom pos ind_sym codom x_str in

  (* STEP 2: Create each clause according to a constructor *)
  (* [case_of cons_sym] creates a clause according to a constructor
     [cons_sym]. *)
  let case_of : sym -> tbox = fun cons_sym ->
    let codom : term list -> tvar list -> tbox -> tbox = fun ts xs _ ->
      prf_of_p (List.map lift ts) (fapp cons_sym (List.rev_map _Vari xs))
    in
    let inj_var : tvar list -> tvar -> tvar = fun _ x -> x in
    let build_rec_hyp : term list -> tvar -> tbox = fun ts x ->
      prf_of_p (List.map lift ts) (_Vari x)
    in
    let domrec : term -> tvar -> tbox -> tbox -> tbox =
      fun a x rec_hyp next ->
      _Prod (lift a) (Bindlib.bind_var x (_Impl rec_hyp next))
    in
    let dom : term -> tvar -> tbox -> tbox = fun a x next ->
      _Prod (lift a) (Bindlib.bind_var x next)
    in
    let f_rec : tbox -> tvar -> tbox -> tbox = fun a _ _ -> a in
    let f_not_rec : tbox -> tvar -> tbox = fun a _ -> a in
    let init : tbox = _Type in
    fold_cons_typ pos codom inj_var build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec init x_str
  in

  (* STEP 3: Create the conclusion of the inductive principle *)
  let codom ts =
    let x = Bindlib.new_var mkfree x_str in
    let t = Bindlib.bind_var x (prf_of_p ts (_Vari x)) in
    _Prod (fapp ind_sym ts) t
  in
  let conclusion = gen_ind_typ_codom pos ind_sym codom x_str in

  (* STEP 4: Create the induction principle *)
  let t =
    List.fold_right (fun a b -> _Impl (case_of a) b) cons_list conclusion
  in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Pretty.pp_ident (Pos.none ("ind_"^ind_sym.sym_name))
      Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t

(** [gen_rec_rules pos ind_sym rec_sym cons_list] returns the p_rules associa-
    ted with an induction principle [rec_sym] of the inductive type [ind_sym]
    (with its constructors [cons_list]). That means the command
    inductive T : Π(i1:A1),...,Π(im:Am), TYPE := c1:T1 | ... | cn:Tn generates
    a rule for each constructor. If Ti = Π(b1:B1), ... , Π(bk:Bk), T then the
    rule for ci is:
    rule ind_T p pic1 ... picn _ ... _ (ci x0 ... x(k-1)) -->
    pici x0 t0? ... x(k-1) t(k-1)?
    with m underscores and tj? = nothing if xj isn't a value of the inductive
    type and tj? = (ind_T p pic1 ... picn _ ... _ xj) if xj is a value of the
    inductive type T (i.e. xj = T v1 ... vm).
    Note: There cannot be name clashes between pattern variable names and
    function symbols names since pattern variables are prefixed by $. *)
let gen_rec_rules : popt -> sym -> sym -> sym list -> p_rule list =
  fun pos ind_sym rec_sym cons_list ->

  (* STEP 1: Create the common head of the rules *)
  let rec_iden = P.iden rec_sym.sym_name in
  let p_patt = P.patt0 "p" in
  let add_arg t s = P.appl t (P.patt0 ("pi" ^ s.sym_name)) in
  let head = P.appl rec_iden p_patt in
  let common_head = List.fold_left add_arg head cons_list in

  (* STEP 2: Create each p_rule according to a constructor *)
  (* [gen_rule_cons cons_sym] creates a p_rule according to a constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> p_rule = fun cons_sym ->
    let codom : term list -> p_term list -> p_term -> p_rule = fun ts xs p ->
      let rec_arg = P.fold_appl (P.iden cons_sym.sym_name) (List.rev xs) in
      let lhs = P.appl (P.appl_wild common_head (List.length ts)) rec_arg in
      if !log_enabled then
        log_ind "The rule [%a] --> %a"
          Pretty.pp_p_term lhs Pretty.pp_p_term p;
      P.rule lhs p
    in
    let inj_var : p_term list -> tvar -> p_term = fun xs _ ->
      P.patt0 ("x" ^ (string_of_int (List.length xs)))
    in
    let build_rec_hyp : term list -> p_term -> p_term = fun ts x ->
      let arg_type = P.appl_wild common_head (List.length ts) in
      P.appl arg_type x
    in
    let domrec : term -> p_term -> p_term -> p_rule -> p_rule =
      fun _ _ _ next -> next
    in
    let dom : term -> p_term -> p_rule -> p_rule = fun _ _ next -> next in
    let f_rec : p_term -> p_term -> p_term -> p_term =
      fun p x rec_hyp -> P.appl (P.appl p x) rec_hyp
    in
    let f_not_rec : p_term -> p_term -> p_term = fun p x -> P.appl p x in
    let init : p_term = P.patt0 ("pi" ^ cons_sym.sym_name) in
    fold_cons_typ pos codom inj_var build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec init ""
  in

  (* STEP 3: Build all the p_rules *)
  List.rev_map gen_rule_cons cons_list
