open Support
module B = Beluga
module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon
module Id = Beluga.Id
module Total = Beluga.Total
module Whnf = B.Whnf

module P = B.Pretty.Int.DefaultPrinter

open B.Syntax.Int

let dprintf, dprint, _ = B.Debug.(makeFunctions' (toFlags [11]))
open B.Debug.Fmt

type t = Theorem.t -> Comp.proof_state -> unit

(** Fill the hole with the given proof.
    This will solve the current subgoal.
 *)
let solve (proof : Comp.proof) : t =
  fun t g ->
  Theorem.solve g proof;
  Theorem.remove_subgoal t g

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
  fun t s ->
  let open Comp in
  let (tau, theta) = s.goal in
  let cD, cG, tau' = intros' names LF.Empty LF.Empty tau in
  (* only create a new intros node if something actually happened *)
  if tau' <> tau then
    let goal' = (tau', theta) in
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
    Theorem.remove_current_subgoal t;
    Theorem.add_subgoal t new_state;
    Comp.intros context (Comp.incomplete_proof new_state)
    |> Theorem.solve s
  else
    Theorem.printf t
      "Nothing to introduce.@,\
       This command works only when the goal is a function type.@,"

(** Calls the coverage checker to compute the list of goals for a
    given type in the contexts of the given proof state.
 *)
let generate_pattern_coverage_goals
      (k : Command.split_kind) (m : Comp.exp_syn) (tau : Comp.typ) (g : Comp.proof_state) t
    : (LF.mctx * B.Coverage.cov_goal * LF.msub) list option =
  let open Comp in
  let cgs =
    B.Coverage.genPatCGoals g.context.cD (B.Coverage.gctx_of_compgctx g.context.cG) (B.Total.strip tau) []
  in
  let n = List.length cgs in
  match k with
  | `invert when n <> 1 ->
     Theorem.printf t "Can't invert %a. (Not a unique case.)@,"
       (P.fmt_ppr_cmp_exp_syn g.context.cD g.context.cG P.l0) m;
     None
  | _ -> Some cgs

let split (k : Command.split_kind) (i : Comp.exp_syn) (tau : Comp.typ) mfs : t =
  let open Comp in
  fun t s ->
  (* Compute the coverage goals for the type to split on. *)
  dprintf
    begin fun p ->
    p.fmt "[harpoon-split] split on %a with type %a"
      (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG P.l0) i
      (P.fmt_ppr_cmp_typ s.context.cD P.l0) tau
    end;
  match generate_pattern_coverage_goals k i tau s t with
  | None -> ()
  (* splitting failed, so we do nothing *)
  | Some cgs ->
     (* We will map get_branch_by f over the coverage goals that were generated.
        get_branch_by f computes the subgoal for the given coverage goal,
        invokes the add_subgoal callback on the computed subgoal (to register it),
        invokes the remove_subgoal callback, and constructs the
        Harpoon syntax for this split branch.
      *)
     let get_branch_by f (cD, cov_goal, t) =
       match cov_goal with
       (* Because we called genPatCGoals, I'm pretty sure that the
          CovCtx and CovGoal constructors are impossible here,
          but I could be wrong.
        *)
       | B.Coverage.CovCtx _
         | B.Coverage.CovGoal (_, _, _) ->
          Misc.not_implemented "CovCtx impossible"
       | B.Coverage.CovPatt (cG, pat, tau_p) ->
          let open Comp in
          let open B in
          let cG = Coverage.compgctx_of_gctx cG in

          let tau_p = Whnf.cnormCTyp tau_p in
          dprintf
            begin fun p ->
            p.fmt "[harpoon-split] @[<v>got pattern type:@,\
                   tau_p = @[%a@]@,\
                   for pattern = @[%a@]@,\
                   in cD = @[%a@]@,\
                   coverage's refinement t =@,\
                   @[%a@]@,\
                   with source context s.context.cD = @,\
                   @[%a@]@]"
              (P.fmt_ppr_cmp_typ cD P.l0) tau_p
              (P.fmt_ppr_cmp_pattern cD cG P.l0) pat
              (P.fmt_ppr_lf_mctx P.l0) cD
              (P.fmt_ppr_lf_msub cD P.l0) t
              (P.fmt_ppr_lf_mctx P.l0) s.context.cD
            end;

          let t', t1', cD_b, pat' =
            (* Refine the pattern to compute the branch's
               meta-context, accounting for dependent pattern matching on
               `m`. *)
            Reconstruct.synPatRefine
              Loc.ghost
              (Reconstruct.case_type i)
              (s.context.cD, cD)
              t
              pat
              (* We possibly need to Total.strip tau here.
                 So far it seems to work as is.
                 -je *)
              (tau, tau_p)
          in
          dprintf
            begin fun p ->
            p.fmt "@[<v 2>[harpoon-split] [after synPatRefine]@,\
                   t' = @[%a@]@,\
                   t1 = @[%a@]@,\
                   cD_b (target ctx) = @[%a@]\
                   @]"
              (P.fmt_ppr_lf_msub cD_b P.l0) t'
              (P.fmt_ppr_lf_msub cD_b P.l0) t1'
              (P.fmt_ppr_lf_mctx P.l0) cD_b
            end;
          (* cD_b |- t' : s.context.cD (outside the branch)
             cD_b |- t1' : cD (inside the branch)
             and recall: cD |- t : s.context cD
           *)
          let refine_ctx_inside ctx = Whnf.cnormCtx (ctx, t1') in
          let refine_ctx_outside ctx = Whnf.cnormCtx (ctx, t') in

          (* Compute the gctx inside the branch.*)
          (* cG is given to use by coverage such that
             cD |- cG
             that is, it exists *inside* the branch
           *)
          let cG_b = refine_ctx_inside cG in
          (* cD_b |- cG_b *)
          let cIH_b =  refine_ctx_outside (Whnf.normCtx s.context.cIH) in
          (* cD_b |- cIH_b *)
          let (cD_b, cIH') =
            if Total.is_inductive_split s.context.cD s.context.cG i && Total.struct_smaller pat'
            then
              (* mark subterms in the context as inductive *)
              let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
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
          dprintf
            begin fun p ->
            p.fmt "[harpoon-split] cD_b = @[%a@]"
              (P.fmt_ppr_lf_mctx P.l0) cD_b
            end;
          (* propagate inductive annotations *)
          dprintf
            begin fun p ->
            p.fmt "[harpoon-split @[<v>s.context.cD = @[%a@]@,\
                   t' = @[%a@]@]"
              (P.fmt_ppr_lf_mctx P.l0) s.context.cD
              (P.fmt_ppr_lf_msub cD_b P.l0) t'
            end;
          let cD = Check.Comp.id_map_ind cD_b t' s.context.cD in
          let cG = Total.mark_gctx cG_b in
          dprintf
            begin fun p ->
            let open Format in
            p.fmt "[harpoon-split] @[<v 2>id_map_ind@,%a@,t'@,%a@,=@,%a@]"
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD_b
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) s.context.cD
              (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD
            end;
          let cIH0 = Total.wf_rec_calls cD cG mfs in
          let cIH = Context.(append cIH_b (append cIH0 cIH')) in
          let context = { cD; cG; cIH } in
          let new_state =
            { context
            ; goal = Pair.rmap (fun s -> Whnf.mcomp s t') s.goal
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
            Theorem.add_subgoal t new_state;
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
            Theorem.add_subgoal t new_state;
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
     Theorem.remove_subgoal t s;
     let revCgs = List.rev cgs in
     (match (List.for_all is_meta_split revCgs, List.for_all is_comp_split revCgs) with
      | (true, false) ->
         List.map get_meta_branch revCgs
         |> Comp.meta_split i tau
      | (false, true) ->
         List.map get_comp_branch revCgs
         |> Comp.comp_split i tau
      | (false, false) ->
         failwith "[split] Mixed cases of meta and comp split"
      | _ ->
         B.Error.violation "[split] Impossible case"
     )
     |> Theorem.solve s

(** Constructs a new proof state from `g` in which the meta-context is
    extended with the given declaration, and the goal type is
    appropriately shifted.
    The solution field of the new proof state will be empty.
 *)
let extending_meta_context decl g =
  let open Comp in
  (* Because we are adding a new declaration to cD, the goal type
     no longer makes sense in the new context. We need to weaken it
     by one.
   *)
  let shift = LF.MShift 1 in
  { context =
      { cD = LF.Dec (g.context.cD, decl)
      ; cG = Whnf.cnormCtx (g.context.cG, shift)
      ; cIH = Whnf.cnormCtx (g.context.cIH, shift)
      }
  ; goal = Pair.rmap (fun t -> Whnf.mcomp t shift) g.goal
  ; solution = None
  }

let extending_comp_context decl g =
  let open Comp in
  { g with
    context =
      { g.context with
        cG = LF.Dec (g.context.cG, decl)
      }
  ; solution = None
  }

(** Solves the current subgoal by keeping it the same, but extending
    the meta context with a new declaration.
    This will appropriately MShift the goal type.
 *)
let solve_with_new_meta_decl decl cmd t g =
  Theorem.solve_by_replacing_subgoal t (extending_meta_context decl g) cmd g

(** Solves the current subgoal by keeping it the same, but extending
    the computational context with a new declaration.
 *)
let solve_with_new_comp_decl decl cmd t g =
  Theorem.solve_by_replacing_subgoal t (extending_comp_context decl g) cmd g

let solve_by_unbox' cmd (cT : Comp.meta_typ) (name : B.Id.name) : t =
  solve_with_new_meta_decl LF.(Decl (name, cT, No)) cmd

let solve_by_unbox (m : Comp.exp_syn) (mk_cmd : Comp.meta_typ -> Comp.command) (tau : Comp.typ) (name : B.Id.name) : t =
  let open Comp in
  fun t g ->
  let {cD; cG; cIH} = g.context in
  match tau with
  | TypBox (_, cT) ->
     solve_by_unbox' [mk_cmd cT] cT name t g
  | _ ->
     Theorem.printf t "@[<v>The expression@,  @[%a@]@,cannot be unboxed as its type@,  @[%a@]@,is not a box.@]"
       (P.fmt_ppr_cmp_exp_syn cD cG P.l0) m
       (P.fmt_ppr_cmp_typ cD P.l0) tau

let unbox (m : Comp.exp_syn) (tau : Comp.typ) (name : B.Id.name) : t =
  let open Comp in
  solve_by_unbox m (fun cT -> Unbox (m, name, cT)) tau name

let invoke (k : Command.invoke_kind) (b : Command.boxity) (m : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
  let open Comp in
  let cmd = By (k, m, name, tau, b) in
  match b with
  | `boxed ->
     solve_with_new_comp_decl (CTypDecl (name, tau, false)) [cmd]
  | `unboxed ->
     solve_by_unbox m (fun _ -> cmd) tau name
