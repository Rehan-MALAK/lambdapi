(** Proofs and tactics. *)

open Timed
open Extra
open Pos
open Terms
open Print

(** Abstract representation of a goal. *)
module Goal :
  sig
    (** Representation of a proof type goal. *)
    type goal_typ = (* TODO have to hide this *)
      { goal_meta : meta  (* Metavariable needing instantiation.          *)
      ; goal_hyps : Env.t (* Precomputed scope for a suitable term.       *)
      ; goal_type : term  (* Precomputed type for a suitable term.        *) }

    (** Representation of a general goal : type, unification *)
    type t =
      | GoalTyp of goal_typ (* The usual proof type goal. *)
      | GoalUnif of constr (* Two terms we'd like equal in some ctxt. *)

    (** [goal_typ_of_meta m] create a goal from the metavariable [m]. *)
    val goal_typ_of_meta : meta -> goal_typ

    (** [get_meta g] returns the metavariable associated to goal [g]. *)
    val get_meta : goal_typ -> meta

    (** [get_type g] returns the environment and expected type of the goal. *)
    val get_type : goal_typ -> Env.t * term

    (** [simpl g] simplifies the given goal, evaluating its type to SNF. *)
    val simpl : goal_typ -> goal_typ

    (** Comparison function. *)
    val compare : goal_typ -> goal_typ -> int
  end =
  struct
    type goal_typ =
      { goal_meta : meta  (* Metavariable needing instantiation.          *)
      ; goal_hyps : Env.t (* Precomputed scope for a suitable term.       *)
      ; goal_type : term  (* Precomputed type for a suitable term.        *) }

    type t =
      | GoalTyp of goal_typ (* The usual proof type goal. *)
      | GoalUnif of constr (* Two terms we'd like equal in ctxt. *)

    let goal_typ_of_meta : meta -> goal_typ = fun m ->
      let (goal_hyps, goal_type) =
        Infer.destruct_prod m.meta_arity !(m.meta_type)
      in
      let goal_type = Eval.simplify (Env.to_ctxt goal_hyps) goal_type in
      {goal_meta = m; goal_hyps; goal_type}

    let get_meta : goal_typ -> meta = fun g -> g.goal_meta

    let get_type : goal_typ -> Env.t * term = fun g ->
      (g.goal_hyps, g.goal_type)

    let simpl : goal_typ -> goal_typ = fun g ->
      {g with goal_type = Eval.snf (Env.to_ctxt g.goal_hyps) g.goal_type}

    let compare : goal_typ -> goal_typ -> int = fun g1 g2 ->
      Meta.compare g1.goal_meta g2.goal_meta
  end

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name     : Pos.strloc  (** Name of the theorem.                 *)
  ; proof_term     : meta        (** Metavariable holding the proof term. *)
  ; proof_goals    : Goal.t list (** Open goals (focused goal is first).  *) }

(** Short synonym for qualified use. *)
type t = proof_state

(** [init name a] returns an initial proof state for a theorem  named
    [name], which statement is represented by the type [a].
    The list of goals is not initialized *)
let init : Pos.strloc -> term -> t = fun name a ->
  let proof_term = fresh_meta ~name:name.elt a 0 in
  {proof_name = name; proof_term; proof_goals = []}

(** [goals_of_meta m] returns a goal associated to the meta m *)
let goals_of_meta : meta -> Goal.t list = fun m ->
  let goal_typ = Goal.GoalTyp (Goal.goal_typ_of_meta m) in
  [goal_typ]

(** [goals_of_typ typ ter] returns a list of goals corresponding to the
    typability of [typ] by a sort and checking eventually that term
    [ter] has type [typ] *)
let goals_of_typ : Pos.popt -> term option -> term option ->
  Goal.t list * term =
  fun pos typ ter ->
  let (typ,sort, to_solve) =
    match typ,ter with
    | Some(typ),Some(ter) ->
      let sort, to_solve2 = Infer.infer [] typ in
      let to_solve =
        match sort with
        | Type | Kind -> Infer.check [] ter typ
        | _ -> Console.fatal pos "%a has type %a (not a sort)."
                 pp_term typ pp_term sort
      in
      typ, sort, to_solve2 @ to_solve
    | None,Some(ter) ->
      let typ,to_solve = Infer.infer [] ter in
      let sort,to_solve2 =
        begin
          match typ with
          | Kind -> Console.fatal pos "Forbidded definition x := _ -> TYPE"
          | _ -> let sort, to_solve2 = Infer.infer [] typ in
            begin
              match sort with
              | Type | Kind -> sort,to_solve2
              | _ -> Console.fatal pos "The term [%a] does not have type \
                                        [%a]." pp_term ter pp_term typ
            end
        end
      in
      typ,sort, to_solve2 @ to_solve
    | Some(typ),None ->
      let sort, to_solve = Infer.infer [] typ in
      begin
        match sort with
        | Type | Kind -> typ,sort,to_solve
        | _ -> Console.fatal pos "%a has type %a (not a sort)."
                 pp_term typ pp_term sort
      end
    | None,None    -> assert false (* already rejected by parser *)
  in
  let to_solve = (* TODO this shoud be removed *)
    try
      Unif.solve {Unif.empty_problem with to_solve}
    with Unif.Unsolvable -> to_solve
  in
  (* aggregate constr list of type of argument *)
(*
  let constr_sort = ([],Type,sort) in
  let goal_sort = [goal_unif constr_sort] in
  (List.map goal_unif to_solve @ goal_sort), typ
*)
  let _sort = sort in
  (List.map (fun x -> Goal.GoalUnif x) to_solve), typ

(** [goals_of_constrs cs] returns a list of unification goals corresponding to a
    list of unification constraints [cs] *)
let goals_of_constrs : constr list -> Goal.t list = fun cs ->
  let goals_unif = List.map (fun x -> Goal.GoalUnif x) cs in
  goals_unif

(** [finished ps] tells whether the proof represented by [ps] is finished. *)
let finished : t -> bool = fun ps -> ps.proof_goals = []

(** [focus_goal ps] returns the focused goal or fails if there is none. *)
let focus_goal : Pos.popt -> proof_state -> Env.t * term = fun pos ps ->
  match List.hd ps.proof_goals with
    | Goal.GoalTyp g       -> Goal.get_type g
    | Goal.GoalUnif _      -> Console.fatal pos "No remaining typing goals..."
    | exception Failure(_) -> Console.fatal pos "No remaining goals..."

(** [pp_goals oc gl] prints the goal list [gl] to channel [oc]. *)
let pp_goals : proof_state pp = fun oc ps ->
  match ps.proof_goals with
  | []    -> Format.fprintf oc " No more goals...\n"
  | g::gs ->
    Format.fprintf oc "\n== Goals ================================\n";
    match g with
    | Goal.GoalTyp g ->
      let (hyps, a) = Goal.get_type g in
      if hyps <> [] then
        begin
          let print_hyp (s,(_,t,_)) =
            Format.fprintf oc "   %s : %a\n" s pp_term (Bindlib.unbox t)
          in
          List.iter print_hyp (List.rev hyps);
          Format.fprintf oc "   --------------------------------------\n"
        end;
      Format.fprintf oc "0. %a\n" pp_term a;
      if gs <> [] then
        begin
          Format.fprintf oc "\n";
          let print_goal i g =
            match g with
            | Goal.GoalTyp g ->
              let (_, a) = Goal.get_type g in
              Format.fprintf oc "%i. %a\n" (i+1) pp_term a
            | Goal.GoalUnif cs -> Format.fprintf oc "Unif? %a\n" pp_constr cs
          in
          List.iteri print_goal gs
        end
    | Goal.GoalUnif cs -> Format.fprintf oc "Unif? %a\n" pp_constr cs;
      if gs <> [] then
        begin
          Format.fprintf oc "\n";
          let print_goal i g =
            match g with
            | Goal.GoalTyp g ->
              let (_, a) = Goal.get_type g in
              Format.fprintf oc "%i. %a\n" (i+1) pp_term a
            | Goal.GoalUnif cs -> Format.fprintf oc "Unif? %a\n" pp_constr cs
          in
          List.iteri print_goal gs
        end
