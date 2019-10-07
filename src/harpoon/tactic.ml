open Support
module B = Beluga
module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon
module Id = Beluga.Id
module Total = Beluga.Total

module P = B.Pretty.Int.DefaultPrinter

open B.Syntax.Int

let dprintf, dprint, _ = B.Debug.(makeFunctions' (toFlags [11]))
open B.Debug.Fmt

type tactic_context =
  { add_subgoal : unit Comp.proof_state -> unit
  ; remove_subgoal : unit Comp.proof_state -> unit
  ; remove_current_subgoal : unit -> unit
  ; printf : 'a. ('a, Format.formatter, unit) format -> 'a
  ; defer : unit -> unit
  }

type t = unit Comp.proof_state -> tactic_context -> unit

(** `solve` with the arguments switched around to make it more
    convenient to call from other tactics.
 *)
let solve' (s : unit Comp.proof_state) (proof : Comp.incomplete_proof) : unit =
  s.Comp.solution <- Some proof

(** Fill the hole with the given proof.
    This will solve the current subgoal.
 *)
let solve (proof : Comp.incomplete_proof) : t =
  fun s tctx ->
  solve' s proof;
  tctx.remove_subgoal s

(** Walks a type and collects assumptions into cD and cG,
    returning the conclusion type.
 *)
let intros' : string list option -> LF.mctx -> Comp.gctx -> Comp.typ ->
              LF.mctx * Comp.gctx * Comp.typ =
  let genVarName tA = B.Store.Cid.Typ.gen_var_name tA in
  let gen_var_for_typ =
    function
    | Comp.TypBox (l, LF.(ClTyp (MTyp tA, psi))) ->
       B.Id.(mk_name (BVarName (genVarName tA)))
    | Comp.TypBox (l, LF.(ClTyp (PTyp tA, psi))) ->
       B.Id.(mk_name (PVarName (genVarName tA)))
    | _ ->
       B.Id.(mk_name NoName)
  in
  let rec go names cD cG t =
    let next_name : (string * string list) option =
      let open Maybe in
      names
      $ function
        | [] -> None
        | x :: xs -> Some (x , xs)
    in
    match t with
    | Comp.TypArr (t1, t2) ->
       let name , names =
         next_name
         |> Maybe.eliminate
              (fun _ -> gen_var_for_typ t1 , None)
              (fun (name, names) -> B.Id.(mk_name (SomeString name)), Some names)
       in
       go names cD (LF.Dec (cG, Comp.CTypDecl (name, t1, false))) t2
    | Comp.TypPiBox (tdec, t2) ->
       go names (LF.Dec (cD, tdec)) cG t2
    | _ -> cD, cG, t
  in
  go


(** Introduces all assumptions present in the current goal.
    Solves the input proof state.
 *)
let intros (names : string list option) : t =
  (* Main body of `intros`: *)
  fun s tctx ->
  let open Comp in
  let (t, sigma) = s.goal in
  let cD, cG, t' = intros' names LF.Empty LF.Empty t in
  (* only create a new intros node if something actually happened *)
  if t' <> t then
    let goal' = (t', sigma) in
    let local_context = {cD; cG; cIH = LF.Empty} in
    let context = B.Context.append_hypotheses s.context local_context in
    let new_state =
      { context
      ; goal = goal'
      ; solution = None
      }
    in
    (* Invoke the callback on the subgoal that we created *)
    (* Solve the current goal with the subgoal. *)
    tctx.remove_current_subgoal ();
    tctx.add_subgoal new_state;
    Comp.intros context (Comp.incomplete_proof new_state)
    |> solve' s
  else
    tctx.printf "Nothing to introduce.@,\
                 This command works only when the goal is a function type.@,"

(** Calls the coverage checker to compute the list of goals for a
    given type in the contexts of the given proof state.
 *)
let generate_pattern_coverage_goals
      (k : Command.split_kind) (m : Comp.exp_syn) (tau : Comp.typ) (g : unit Comp.proof_state) (tctx : tactic_context)
    : (LF.mctx * B.Coverage.cov_goal * LF.msub) list option =
  let open Comp in
  let cgs =
    B.Coverage.genPatCGoals g.context.cD (B.Coverage.gctx_of_compgctx g.context.cG) (B.Total.strip tau) []
  in
  let n = List.length cgs in
  match k with
  | `invert when n <> 1 ->
     tctx.printf "Can't invert %a. (Not a unique case.)@,"
       (P.fmt_ppr_cmp_exp_syn g.context.cD g.context.cG P.l0) m;
     None
  | _ -> Some cgs

let split (k : Command.split_kind) (m : Comp.exp_syn) (tau : Comp.typ) mfs : t =
  let open Comp in
  fun s tctx ->
  (* Compute the coverage goals for the type to split on. *)
  dprintf
    begin fun p ->
    p.fmt "[harpoon-split] split on %a with type %a"
      (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG P.l0) m
      (P.fmt_ppr_cmp_typ s.context.cD P.l0) tau
    end;
  match generate_pattern_coverage_goals k m tau s tctx with
  | None -> ()
  (* splitting failed, so we do nothing *)
  | Some cgs ->
     (* We will map get_branch_by f over the coverage goals that were generated.
        get_branch_by f computes the subgoal for the given coverage goal,
        invokes the add_subgoal callback on the computed subgoal (to register it),
        invokes the remove_subgoal callback, and constructs the
        Harpoon syntax for this split branch.
      *)
     let get_branch_by f (cD, cov_goal, ms) =
       match cov_goal with
       (* Because we called genPatCGoals, I'm pretty sure that the
          CovCtx and CovGoal constructors are impossible here,
          but I could be wrong.
        *)
       | B.Coverage.CovCtx _
         | B.Coverage.CovGoal (_, _, _) ->
          Misc.not_implemented "CovCtx impossible"
       | B.Coverage.CovPatt (cG, pat, tau) ->
          let open Comp in
          (* compute the head of the pattern to be the case label
             We do this right away since it could fail if the user
             did something funny.
           *)
          let open B in
          let refine_ctx ctx = Whnf.cnormCtx (Whnf.normCtx ctx, ms) in
          let cG = Coverage.compgctx_of_gctx cG in
          let cIH = refine_ctx s.context.cIH in
          dprintf
            begin fun p ->
            p.fmt "[harpoon-split] got pattern @[%a@]"
              (P.fmt_ppr_cmp_pattern cD cG P.l0) pat
            end;
          let (cDext, cIH') =
            if Total.is_comp_inductive cG m && Total.struct_smaller pat
            then
              (* mark subterms in the context as inductive *)
              let cD1 = Check.Comp.mvars_in_patt cD pat in
              (* Compute the well-founded recursive calls *)
              let cIH = Total.wf_rec_calls cD1 LF.Empty mfs in
              dprintf
                begin fun p ->
                p.fmt "[harpoon-split] @[<v>computed WF rec calls:@,@[<hov>%a@]@]"
                  (P.fmt_ppr_cmp_gctx cD P.l0) cIH
                end;
              (cD1, cIH)
            else
              begin
                dprint
                  begin fun _ ->
                  "[harpoon-split] skipped computing WF calls; splitting on non-inductive variable"
                  end;
                (cD, LF.Empty)
              end
          in
          (* propagate inductive annotations *)
          let cD = Check.Comp.id_map_ind cDext ms s.context.cD in
          let cG = Total.mark_gctx cG in
          dprintf
            begin fun p ->
            let open Format in
            p.fmt "[harpoon-split] @[<v 2>id_map_ind@,%a@,ms@,%a@,=@,%a@]"
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cDext
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) s.context.cD
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD
            end;
          let cIH0 = Total.wf_rec_calls cD cG mfs in
          let cIH = Context.(append cIH (append cIH0 cIH')) in
          let context = { cD; cG; cIH } in
          let new_state =
            { context
            ; goal = Pair.rmap (fun s -> Whnf.mcomp s ms) s.goal
            ; solution = None
            }
          in
          f context new_state pat
     in

     let get_meta_branch =
       get_branch_by
         begin fun context new_state pat ->
         (* compute the head of the pattern to be the case label *)
         match pat with
         | PatMetaObj (_, patt) ->
            let c =
              head_of_meta_obj patt
              |> Maybe.get
              |> Pair.lmap B.Context.hatToDCtx
            in
            tctx.add_subgoal new_state;
            meta_branch c context (incomplete_proof new_state)
         | _ ->
            B.Error.violation "[get_meta_branch] Impossible case"
         end
     in

     let get_comp_branch =
       get_branch_by
         begin fun context new_state pat ->
         match pat with
         | PatConst (_, cid, _) ->
            tctx.add_subgoal new_state;
            comp_branch cid context (incomplete_proof new_state)
         | _ ->
            B.Error.violation "[get_meta_branch] Impossible case"
         end
     in

     let is_meta_split =
       function
       | (_, B.Coverage.CovPatt (_, PatMetaObj _, _), _) -> true
       | _ -> false
     in
     let is_comp_split cg = not (is_meta_split cg) in
     tctx.remove_subgoal s;
     let revCgs = List.rev cgs in
     (match (List.for_all is_meta_split revCgs, List.for_all is_comp_split revCgs) with
      | (true, false) ->
         List.map get_meta_branch revCgs
         |> Comp.meta_split m tau
      | (false, true) ->
         List.map get_comp_branch revCgs
         |> Comp.comp_split m tau
      | (false, false) ->
         failwith "[split] Mixed cases of meta and comp split"
      | _ ->
         B.Error.violation "[split] Impossible case"
     )
     |> solve' s

let unbox (m : Comp.exp_syn) (tau : Comp.typ) (name : B.Id.name) : t =
  let open Comp in
  fun g tctx ->
  let {cD; cG; cIH} = g.context in
  match tau with
  | TypBox (_, cT) ->
     let open B in
     (* Because we are adding a new declaration to cD, the goal type
        no longer makes sense in the new context. We need to weaken it
        by one.
      *)
     let shift = LF.MShift 1 in
     let new_state =
       { context =
           { cD = LF.(Dec (cD, Decl (name, cT, No)))
           ; cG = Whnf.cnormCtx (cG, shift)
           ; cIH = Whnf.cnormCtx (cIH, shift)
           }
       ; goal = Pair.rmap (fun t -> Whnf.mcomp t shift) g.goal
       ; solution = None
       }
     in
     tctx.remove_current_subgoal ();
     tctx.add_subgoal new_state;
     prepend_commands
       [ Unbox (m, name, cT) ]
       (Comp.incomplete_proof new_state)
     |> solve' g
  | _ ->
     tctx.printf "@[<v>The expression@,  %a@, cannot be unboxed as its type@,  %a@, is not a box.@]"
       (P.fmt_ppr_cmp_exp_syn cD cG P.l0) m
       (P.fmt_ppr_cmp_typ cD P.l0) tau

let solve_with_new_decl decl cmd g tctx =
  let open Comp in
  let new_state =
    { g with
      context =
        { g.context with
          cG = LF.Dec ( g.context.cG , decl)
        }
    ; solution = None
    }
  in
  tctx.remove_current_subgoal ();
  tctx.add_subgoal new_state;
  prepend_commands
    [ cmd ]
    (Comp.incomplete_proof new_state)
  |> solve' g

let invoke (k : Command.invoke_kind) (m : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
  let open Comp in
  solve_with_new_decl (CTypDecl (name, tau, false)) (Comp.By (k, m, name, tau))
