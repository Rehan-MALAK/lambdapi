(** Toplevel commands. *)

open Extra
open Console
open Terms
open Pos
open Syntax
open Proof
open Print

(** Logging function for tactics. *)
let log_tact = new_logger 't' "tact" "tactics"
let log_tact = log_tact.logger

(** [solve ps pos] calls the default solve algorithm on the unification
    goals of the proof state [ps] and does not fail *)
let solve ps pos =
  try
    let gs_typ,gs_unif = List.partition Goal.is_typ ps.proof_goals in
    let to_solve = List.map Goal.constr_of gs_unif in
    let new_cs = Unif.solve {Unif.empty_problem with to_solve} in
    let new_gs_unif = List.map Goal.unif new_cs in
    {ps with proof_goals = new_gs_unif @ gs_typ}
  with
  | Unif.Unsolvable ->
    fatal pos "Constraints are unsolvable !"

(** [handle_tactic ss ps tac] tries to apply the tactic [tac] (in the proof
     state [ps]), and returns the new proof state.  This function fails
     gracefully in case of error. *)
let handle_tactic :
  Sig_state.t -> Terms.expo -> Proof.t -> p_tactic -> Proof.t =
  fun ss e ps tac ->
  (* First handle the tactics that do not change the goals. *)
  match tac.elt with
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" pp_goals ps; ps
  | P_tac_proofterm     ->
      (* Just print the current proof term. *)
      let t = Meta(ps.proof_term, [||]) in
      let name = ps.proof_name.elt in
      Console.out 1 "Proof term for %s: %a\n" name pp_term t; ps
  | P_tac_query(q)      ->
      Queries.handle_query ss (Some ps) q; ps
  | _                   ->
  (* The other tactics may change the goals. *)
  (* Get the focused goal and the other goals. *)
    if ps.proof_goals = [] then
      fatal tac.pos "There is nothing left to prove.";

  match tac.elt with
  | P_tac_print
  | P_tac_proofterm
  | P_tac_query(_)      -> assert false (* Handled above. *)
  | P_unif_solve        -> solve ps tac.pos
  | _                   ->

  (* Get the unif goals, the first type goal and the following goals *)
  let pre_g, g, post_g =
    let rec first_goal_typ pre post =
      match post with
      | [] -> pre,None,post
      | (Goal.Typ gt) :: post -> pre,Some(gt),post
      | (Goal.Unif _ as gu) :: post -> first_goal_typ (pre @ [gu]) post
    in
    first_goal_typ [] ps.proof_goals
  in

  (* Obtaining the goal environment and type. *)
  let scope t =
    let (env, _a) = match g with
      | Some gt -> Goal.get_type gt
      | None -> assert false
    in
    let tt = Scope.scope_term e ss env t in
    env, tt
  in

  let handle_refine : Proof.t -> term -> Proof.t = fun ps t ->
    (* Check if the goal metavariable appears in [t]. *)
    let ((env, a), m) = match g with
      | Some gt -> (Goal.get_type gt),(Goal.get_meta gt)
      | None -> assert false
    in
    log_tact "refining [%a] with term [%a]" pp_meta m pp_term t;
    if Basics.occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    log_tact "proving %a" pp_typing (Env.to_ctxt env, t, a);
    let to_solve = Infer.check (Env.to_ctxt env) t a in
    let to_solve =
      try
        Unif.solve {Unif.empty_problem with to_solve}
      with Unif.Unsolvable -> to_solve
    in
    let gs_unif = List.map Goal.unif to_solve in
    (* Instantiation. *)
    set_meta m (Bindlib.unbox (Bindlib.bind_mvar (Env.vars env) (lift t)));
    (* New subgoals and focus. *)
    let metas = Basics.get_metas true t in
    let add_goal m = List.insert Goal.compare (Goal.goal_typ_of_meta m) in
    let new_typ_goals = MetaSet.fold add_goal metas [] in
    (* New goals must appear first. *)
    let proof_goals =
      pre_g @ gs_unif @ (List.map Goal.typ new_typ_goals) @ post_g
    in
    {ps with proof_goals}
  in

  match tac.elt with
  | P_tac_print
  | P_tac_proofterm
  | P_tac_query(_)
  | P_unif_solve        -> assert false (* Handled above. *)
  | P_tac_focus(i)      ->
     (* Put the [i]-th goal in focus (if possible). *)
     let rec swap i acc gs =
       match (i, gs) with
       | (0, g::gs) -> g :: List.rev_append acc gs
       | (i, g::gs) -> swap (i-1) (g::acc) gs
       | (_, _    ) -> fatal tac.pos "Invalid goal index."
     in
     {ps with proof_goals = swap i [] ps.proof_goals}
  | P_tac_refine(t)     ->
    let (_, tt) = scope t in
      handle_refine ps tt
  | P_tac_intro(xs)     ->
      let t = Pos.none (P_Abst([(xs,None,false)], Pos.none P_Wild)) in
      let _,tt = scope t in
      handle_refine ps tt
  | P_tac_apply(pt)      ->
      let env,t = scope pt in
      (* Infer the type of [t] and count the number of products. *)
      (* NOTE there is room for improvement here. *)
      let (a, to_solve) = Infer.infer (Env.to_ctxt env) t in
      let goal_sort_unif = List.map Goal.unif to_solve in
      let ps = {ps with proof_goals = goal_sort_unif @ ps.proof_goals} in
      let nb = Basics.count_products a in
      (* Refine using [t] applied to [nb] wildcards (metavariables). *)
      (* NOTE it is scoping that handles wildcards as metavariables. *)
      let rec add_wilds pt n =
        match n with
        | 0 -> let _,tt = scope pt in tt
        | _ -> add_wilds (Pos.none (P_Appl(pt, Pos.none P_Wild))) (n-1)
      in
      handle_refine ps (add_wilds pt nb)
  | P_tac_simpl         ->
    begin
      match g with
      | Some gt ->
        let new_goal_typ = Goal.Typ (Goal.simpl gt) in
        let proof_goals = pre_g @ [new_goal_typ] @ post_g in
        {ps with proof_goals}
      | None    ->
        wrn tac.pos "No goal typ";
        ps
    end
  | P_tac_rewrite(b,po,t) ->
    let env,tt = scope t in
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      handle_refine ps (Rewrite.rewrite ss tac.pos ps b po tt)
  | P_tac_refl          ->
      handle_refine ps (Rewrite.reflexivity ss tac.pos ps)
  | P_tac_sym           ->
      handle_refine ps (Rewrite.symmetry ss tac.pos ps)
  | P_tac_why3(config)  ->
    begin
      match g with
      | Some gt ->
        let t = Why3_tactic.handle ss tac.pos config (Goal.Typ gt) in
        handle_refine ps t
      | None -> wrn tac.pos "No goal typ" ; ps
    end
  | P_tac_fail          ->
      fatal tac.pos "Call to tactic \"fail\""

let handle_tactic :
  Sig_state.t -> Terms.expo -> Proof.t -> p_tactic -> Proof.t =
  fun ss exp ps tac ->
  try handle_tactic ss exp ps tac
  with Fatal(_,_) as e ->
    let _ = handle_tactic ss exp ps (none P_tac_print) in
    raise e
