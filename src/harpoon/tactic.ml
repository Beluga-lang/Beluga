open Support
module B = Beluga
module Context = B.Context
module Comp = Beluga.Syntax.Int.Comp
module S = B.Substitution
module Command = Beluga.Syntax.Ext.Harpoon
module Id = Beluga.Id
module Total = Beluga.Total
module Whnf = B.Whnf
module U = B.Unify.StdTrail

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

(** Decides whether the name of the given declaration already occurs
    in the given context.
    A message is displayed if it does.
 *)
let check_variable_uniqueness variable_kind ctx decl name_of_decl print t =
  let name = name_of_decl decl in
  let p d = Id.equals (name_of_decl d) name in
  match Context.find_rev' ctx p with
  | Some d ->
     Theorem.printf t
       "- @[<v>Error: Defining the %s %a is forbidden@ as it overshadows \
        the declaration@,  @[%a@]@]"
       variable_kind
       Id.print name
       print d;
     `duplicate
  | None -> `unique

let check_computational_variable_uniqueness cD cG decl =
  check_variable_uniqueness "computational variable" cG decl
    Comp.name_of_ctyp_decl
    P.(fmt_ppr_cmp_ctyp_decl cD l0)

let check_metavariable_uniqueness cD decl =
  check_variable_uniqueness "metavariable" cD decl
    LF.name_of_ctyp_decl
    P.(fmt_ppr_lf_ctyp_decl cD l0)

type intros'_failure =
  | DuplicatedNames
  | NothingToIntro

(** Walks a type and collects assumptions into cD and cG,
    returning the conclusion type.

    intros' names cD cG tau = cD' cG' tau'
    such that:
    - cD' is an extension of cD obtained from all the Pi-types in tau;
    - cG' is an extension of cG obtained from all the simple function
      types in tau.

    The given optional names are used for the introduced arguments.
    Else, fresh names are generated internally.
 *)
let intros' : Theorem.t ->
              string list option -> LF.mctx -> Comp.gctx -> Comp.typ ->
              (intros'_failure, LF.mctx * Comp.gctx * Comp.typ) Either.t =
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
  fun t ->
  let rec go updated names cD cG tau =
    let next_name = Maybe.(names $ Misc.List.uncons) in
    match tau with
    | Comp.TypArr (_, tau_1, tau_2) ->
       let (name, names) =
         next_name
         |> Maybe.eliminate
              (fun _ -> gen_var_for_typ tau_1 , None)
              (fun (name, names) -> B.Id.(mk_name (SomeString name)), Some names)
       in
       let d = Comp.CTypDecl (name, tau_1, false) in
       begin match check_computational_variable_uniqueness cD cG d t with
       | `unique -> go true names cD (LF.Dec (cG, d)) tau_2
       | `duplicate -> Either.Left DuplicatedNames
       end
    | Comp.TypPiBox (_, d, tau_2) ->
       begin match check_metavariable_uniqueness cD d t with
       | `unique -> go true names (LF.Dec (cD, d)) cG tau_2
       | `duplicate -> Either.Left DuplicatedNames
       end
    | _ when updated -> Either.Right (cD, cG, tau)
    | _ -> Either.Left NothingToIntro
  in
  go false


(** Introduces all assumptions present in the current goal.
    Solves the input proof state.
 *)
let intros (names : string list option) : t =
  (* Main body of `intros`: *)
  fun t s ->
  let open Comp in
  let (tau, theta) = s.goal in
  match intros' t names LF.Empty LF.Empty tau with
  | Either.Right (cD, cG, tau') ->
     (* only create a new intros node if something actually happened *)
     let goal = (tau', theta) in
     let local_context = {cD; cG; cIH = LF.Empty} in
     let context = Whnf.append_hypotheses s.context local_context in
     let new_state =
       { context
       ; goal
       ; solution = None
       ; label = s.label
       }
     in
     (* Invoke the callback on the subgoal that we created *)
     (* Solve the current goal with the subgoal. *)
     Theorem.solve_by_replacing_subgoal t new_state (Comp.intros context) s
  | Either.Left NothingToIntro ->
     Theorem.printf t
       "Nothing to introduce.@,\
        The intros tactic works only when the goal is a function type.@,"

  | Either.Left DuplicatedNames ->
     Theorem.printf t "Error: intros failed@,"

let is_valid_goals_for_split_kind k cgs =
  let n = List.length cgs in
  match k with
  | `invert when n <> 1 -> `cant_invert
  | `impossible when n <> 0 -> `not_impossible
  | _ -> `ok

let make_subgoal_path_for_split_kind k label parent_label =
  match k with
  | `invert -> parent_label (* ignore new label for inversion *)
  | `impossible ->
     B.Error.violation
       "[harpoon-split] there should be no subgoals for impossible splits"
  | `split -> label :: parent_label

(** Calls the coverage checker to compute the list of goals for a
    given type in the contexts of the given proof state.

    g is a proof state containing cD such that
    - cD |- tau <== type
 *)
let generate_pattern_coverage_goals
      (tau : Comp.typ) (g : Comp.proof_state) t
    : (LF.mctx * B.Coverage.cov_goal * LF.msub) list =
  let open Comp in
  let cgs =
    B.Coverage.genPatCGoals g.context.cD (B.Coverage.gctx_of_compgctx g.context.cG) (B.Total.strip tau) []
  in
  cgs

let split (k : Command.split_kind) (i : Comp.exp_syn) (tau : Comp.typ) mfs : t =
  let open B in
  let open Comp in
  fun t s ->
  (* Compute the coverage goals for the type to split on. *)
  dprintf
    begin fun p ->
    p.fmt "[harpoon-split] @[<v>@[%a@] on @[%a@]@,\
           with type @[%a@]@]"
      P.fmt_ppr_cmp_split_kind k
      (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG P.l0) i
      (P.fmt_ppr_cmp_typ s.context.cD P.l0) tau
    end;
  (* hack for parameter variables, as usual *)
  let _, tau, _ =
    match i, tau with
    | AnnBox ((_, mC), _), TypBox (loc, mT) ->
       let k, mT', p_opt = Check.Comp.fixParamTyp mC mT in
       dprintf
         begin fun p ->
         p.fmt "[harpoon-split] fixed parameter variable type: @[%a@]"
           (P.fmt_ppr_cmp_meta_typ s.context.cD) mT
         end;
       k, TypBox(loc, mT'), p_opt
    | _ -> None, tau, None
  in
  let cgs = generate_pattern_coverage_goals tau s t in
  match is_valid_goals_for_split_kind k cgs with
  | `cant_invert ->
     Theorem.printf t "Can't invert @[%a@]. (Not a unique case.)@,"
       (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG P.l0) i
  | `not_impossible ->
     Theorem.printf t "Can't eliminate @[%a@] as impossible@ as its type\
                       @,  @[%a@]@,\
                       cannot be shown to be empty."
       (P.fmt_ppr_cmp_exp_syn s.context.cD s.context.cG P.l0) i
       (P.fmt_ppr_cmp_typ s.context.cD P.l0) tau
  | `ok ->
     dprintf
       begin fun p ->
       p.fmt "[harpoon-split] generated %d cases"
         (List.length cgs)
       end;
     (* We will map get_branch over the coverage goals that were generated.
        get_branch_by f computes the subgoal for the given coverage goal,
        invokes the add_subgoal callback on the computed subgoal (to register it),
        invokes the remove_subgoal callback, and constructs the
        Harpoon syntax for this split branch.
      *)
     let get_branch (cD, cov_goal, t) =
       match cov_goal with
       (* Because we called genPatCGoals, I'm pretty sure that the
          CovCtx and CovGoal constructors are impossible here,
          but I could be wrong.
        *)
       | B.Coverage.CovCtx _
         | B.Coverage.CovGoal (_, _, _) ->
          B.Error.violation "getPatCGoals must return CovPatt coverage goals"
       | B.Coverage.CovPatt (cG, pat, tau_p) ->
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

          let t', t1', cD_b =
            (* Refine the pattern to compute the branch's
               meta-context, accounting for dependent pattern matching on
               `m`. *)
            dprintf
              begin fun p ->
              p.fmt "[harpoon-split] @[<v>before synPatRefine:@,\
                     cD = @[%a@]@,\
                     cD' = @[%a@]@,\
                     cD' |- t : cD = @[%a@]@,\
                     pat1 = @[%a@]@,\
                     tau_s = @[%a@]@,\
                     tau1 = @[%a@]@]"
                (P.fmt_ppr_lf_mctx P.l0) s.context.cD
                (P.fmt_ppr_lf_mctx P.l0) cD
                (P.fmt_ppr_lf_msub cD P.l0) t
                (P.fmt_ppr_cmp_pattern cD cG P.l0) pat
                (P.fmt_ppr_cmp_typ s.context.cD P.l0) tau
                (P.fmt_ppr_cmp_typ cD P.l0) tau_p
              end;
            Reconstruct.synPatRefine
              Loc.ghost
              (Reconstruct.case_type (lazy pat) i)
              (s.context.cD, cD)
              t
              (* We possibly need to Total.strip tau here.
                 So far it seems to work as is.
                 -je *)
              (tau, tau_p)
          in
          let pat' = Whnf.cnormPattern (pat, t1') in
          dprintf
            begin fun p ->
            p.fmt "@[<v 2>[harpoon-split] [after synPatRefine]@,\
                   t' = @[<v>@[%a@]@,: @[%a@]@]@,\
                   t1 = @[<v>@[%a@]@,: @[%a@]@]@,\
                   cD_b (target ctx) = @[%a@]@,\
                   @]"
              (P.fmt_ppr_lf_msub cD_b P.l0) t'
              (P.fmt_ppr_lf_mctx P.l0) s.context.cD
              (P.fmt_ppr_lf_msub cD_b P.l0) t1'
              (P.fmt_ppr_lf_mctx P.l0) cD
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

          dprintf
            begin fun p ->
            p.fmt "[harpoon-split] @[<v>refined cG and cIH@,\
                   cG_b = @[%a@]@,\
                   cIH = <elided>@,\
                   pat' = @[%a@]@]"
              (P.fmt_ppr_cmp_gctx cD_b P.l0) cG_b
              (P.fmt_ppr_cmp_pattern cD_b cG_b P.l0) pat'
            end;

          (* cD_b |- cIH_b *)
          let (cD_b, cIH') =
            if Total.is_inductive_split s.context.cD s.context.cG i && Total.struct_smaller pat'
            then
              let _ =
                dprintf
                  begin fun p ->
                  p.fmt "[harpoon-split] @[<v>marking subterms inductive in:@,\
                         cD_b = @[%a@]@,\
                         where pat' = @[%a@]@]"
                    P.(fmt_ppr_lf_mctx l0) cD_b
                    P.(fmt_ppr_cmp_pattern cD_b cG_b l0) pat'
                  end
              in
              (* mark subterms in the context as inductive *)
              let cD1 = Check.Comp.mvars_in_patt cD_b pat' in
              dprintf
                begin fun p ->
                p.fmt "[harpoon-split] @[<v>mvars_in_pat cD_b pat':@,\
                       cD1 = @[%a@]@]"
                  P.(fmt_ppr_lf_mctx l0) cD1
                end;
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
                (cD_b, LF.Empty)
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
            p.fmt "[harpoon-split] @[<v>s.context.cD = @[%a@]@,\
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
          let new_state case_label =
            { context
            ; goal = Pair.rmap (fun s -> Whnf.mcomp s t') s.goal
            ; solution = None
            ; label =
                make_subgoal_path_for_split_kind k
                  ("split (case " ^ case_label ^ ")")
                  s.label
            }
          in
          (context, new_state, pat')
     in

     let make_context_branch (context, new_state, pat) =
       match pat with
       | PatMetaObj (_, (_, LF.CObj cPsi)) ->
          let case_label =
            match cPsi with
            | LF.Null -> EmptyContext Loc.ghost
            | LF.(DDec (CtxVar _, TypDecl (x, tA))) ->
               ExtendedBy (Loc.ghost, Whnf.cnormTyp (tA, Whnf.m_id))
            | _ -> B.Error.violation "[get_context_branch] pattern not a context"
          in
          let label =
            Fmt.stringify
              P.(fmt_ppr_cmp_context_case
                 (fmt_ppr_lf_typ context.cD LF.Null l0))
              case_label
          in
          let s' = new_state label in
          Theorem.add_subgoal t s';
          context_branch case_label context (incomplete_proof s')
       | _ -> assert false
     in
     let make_meta_branch (context, new_state, pat) =
       match pat with
       | PatMetaObj (_, (_, LF.ClObj (cPsi, tM))) ->
          let label, c =
            let LF.(MObj (Root (_, h, _))) = tM in
            ( Fmt.stringify P.(fmt_ppr_lf_head context.cD LF.Null l0) h
            , (B.Context.hatToDCtx cPsi, h)
            )
          in
          let s' = new_state label in
          Theorem.add_subgoal t s';
          meta_branch c context (incomplete_proof s')
       | _ -> B.Error.violation "[make_meta_branch] pattern not a meta object"
     in
     let make_comp_branch (context, new_state, pat) =
       match pat with
       | PatConst (_, cid, _) ->
          let label = Store.Cid.DefaultRenderer.render_cid_comp_const cid in
          let s' = new_state label in
          Theorem.add_subgoal t s';
          comp_branch cid context (incomplete_proof s')
       | _ ->
          B.Error.violation "[get_context_branch] pattern not a constant"
     in

     let decide_split_kind =
       function
       | _, B.Coverage.CovPatt (_, PatMetaObj (_, LF.(_, CObj _)), _), _ -> `context
       | _, B.Coverage.CovPatt (_, PatMetaObj (_, LF.(_, ClObj (_, _))), _), _ -> `meta
       | _, B.Coverage.CovPatt (_, PatConst (_, _, _), _), _ -> `comp
       | _ -> B.Error.violation "unhandled pattern type for split"
     in
     let revCgs = List.rev cgs in
     match
       List.map decide_split_kind revCgs
       |> Nonempty.of_list
       |> Maybe.map Nonempty.all_equal
     with
     | None ->
        Theorem.remove_subgoal t s;
        impossible_split i |> Theorem.solve s
     | Some None ->
        B.Error.violation "mixed cases in split (bug in coverage?)"
     | Some (Some k) ->
        Theorem.remove_subgoal t s;
        let finish f g =
          let f' cg = f (get_branch cg) in
          List.map f' revCgs |> g i tau |> Theorem.solve s
        in
        match k with
        | `meta -> finish make_meta_branch Comp.meta_split
        | `comp -> finish make_comp_branch Comp.comp_split
        | `context -> finish make_context_branch Comp.context_split

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
  ; label = g.label
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
    This will appropriately MShift the goal type and the computational
    context.
 *)
let solve_with_new_meta_decl decl f t g =
  let Comp.{cD; _} = Comp.(g.context) in
  match check_metavariable_uniqueness cD decl t with
  | `duplicate -> ()
  | `unique ->
     Theorem.solve_by_replacing_subgoal t (extending_meta_context decl g) f g

(** Solves the current subgoal by keeping it the same, but extending
    the computational context with a new declaration.
 *)
let solve_with_new_comp_decl decl f t g =
  let Comp.{cD; cG; _} = Comp.(g.context) in
  match check_computational_variable_uniqueness cD cG decl t with
  | `duplicate -> ()
  | `unique ->
     Theorem.solve_by_replacing_subgoal t (extending_comp_context decl g) f g

let solve_by_unbox' f (cT : Comp.meta_typ) (name : B.Id.name) : t =
  solve_with_new_meta_decl LF.(Decl (name, cT, No)) f

let solve_by_unbox (m : Comp.exp_syn) (mk_cmd : Comp.meta_typ -> Comp.command) (tau : Comp.typ) (name : B.Id.name) : t =
  let open Comp in
  fun t g ->
  let {cD; cG; cIH} = g.context in
     match tau with
     | TypBox (_, cT) ->
        solve_by_unbox' (prepend_commands [mk_cmd cT]) cT name t g
     | _ ->
        Theorem.printf t
          "@[<v>The expression@,  @[%a@]@,\
           cannot be unboxed as its type@,  @[%a@]@,is not a box.@]"
          (P.fmt_ppr_cmp_exp_syn cD cG P.l0) m
          (P.fmt_ppr_cmp_typ cD P.l0) tau

let unbox (m : Comp.exp_syn) (tau : Comp.typ) (name : B.Id.name) : t =
  let open Comp in
  solve_by_unbox m (fun cT -> Unbox (m, name, cT)) tau name

let invoke (k : Command.invoke_kind) (b : Comp.boxity)
      (m : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
  let open Comp in
  let cmd = By (k, m, name, tau, b) in
  match b with
  | `boxed ->
     solve_with_new_comp_decl (CTypDecl (name, tau, false)) (prepend_commands [cmd])
  | `unboxed ->
     solve_by_unbox m (fun _ -> cmd) tau name

let suffices (i : Comp.exp_syn) (tau_args : Comp.typ list) (tau : Comp.typ) : t =
  (* Processes all leading Pis to replace them with unification
     variables in the following type, and returns the part after all the
     pis.

     Given cD |- tau
     and tau = Pi X_1:U_1. ... Pi X_n:U_n. tau'
     such that tau' contains no more Pis,
     decompose_function tau (internally) computes an msub
     t such that
     cD |- t : cD, X_1:U_1
     that replaces each X_i with a fresh ?X_i.
     The msub t is applied to tau' and tau' is returned.
   *)
  let decompose_function_type cD : Comp.typ -> (Comp.typ list * Comp.typ) option =
    let open Maybe in
    (* Checks that there are no interleaved Pis later and splits
       nested arrow types into a list of input types and one output type.
       Returns None if the type contained interleaved Pis (invalid type).
     *)
    let rec decomp_arrows : Comp.typ -> (Comp.typ list * Comp.typ) option =
      function
      | Comp.TypArr (_, tau_1, tau_2) ->
         decomp_arrows tau_2
         $> fun (inputs, output) -> (tau_1 :: inputs, output)
      | Comp.TypPiBox (_, _, _) -> None
      | tau -> Some ([], tau) (* base type *)
    in
    let rec decomp_pis (t : LF.msub) : Comp.typ -> Comp.tclo = function
      | Comp.TypPiBox (_, d, tau) ->
         let u = Whnf.new_mmvar_for_ctyp_decl cD d in
         let t' =
           let open LF in
           MDot
             ( ClObj
                 ( null_hat
                 , MObj (head (MMVar (mm_var_inst u Whnf.m_id S.LF.id)))
                 )
             , t
             )
         in
         decomp_pis t' tau
      | tau -> (tau, t)
    in
    let open Misc.Function in
    decomp_arrows ++ Whnf.cnormCTyp ++ decomp_pis Whnf.m_id
  in
  fun t s ->
  let open Comp in
  let open Maybe in
  match decompose_function_type s.context.cD tau with
  | None ->
     Theorem.printf t "Failed to decompose function type." (* TODO better error *)
  | Some (tau_args', tau_out) ->
     let unify tau_1 tau_2 =
       try
         dprintf
           begin fun p ->
           p.fmt "[tactic] [suffices] @[<v>unifying @[%a@]@,\
                  against @[%a@]@]"
             P.(fmt_ppr_cmp_typ s.context.cD l0) tau_1
             P.(fmt_ppr_cmp_typ s.context.cD l0) tau_2
           end;
         U.unifyCompTyp s.context.cD
           (tau_1, Whnf.m_id)
           (tau_2, Whnf.m_id)
         |> pure
       with
       | U.Failure msg ->
          None
     in
     (* Unify all argument types. iter2 will raise if there is a mismatch in lengths *)
     match
       try Some (List.map2 (fun x y () -> unify x y) tau_args' tau_args)
       with Invalid_argument _ -> None
     with
     | None ->
        Theorem.printf t "Argument lengths mismatched."
     | Some fs ->
        match traverse_ (fun f -> f ()) fs with
        | None ->
           Theorem.printf t "Failed to unify arguments."
        | Some () ->
           match
             unify (Whnf.cnormCTyp s.goal) tau_out
           with
           | None ->
              Theorem.printf t "Failed to unify goal."
           | Some () ->
              (* TODO Verify that there are no leftover variables *)
              Theorem.remove_subgoal t s;
              (* generate the subgoals for the arguments.
                 by unification it doesn't matter which list we use. *)
              let lemma_name =
                Fmt.stringify
                  P.(fmt_ppr_cmp_exp_syn s.context.cD s.context.cG l0)
                  i
              in
              let subproofs =
                Misc.Function.flip List.mapi tau_args
                  begin fun k tau ->
                  let new_state =
                    { context = s.context
                    ; goal = (tau, Whnf.m_id)
                    ; solution = None
                    ; label =
                        ("premise " ^ string_of_int (k + 1)
                         ^ " of " ^ lemma_name)
                        :: s.label
                    }
                  in
                  Theorem.add_subgoal t new_state;
                  (tau, incomplete_proof new_state)
                  end
              in
              suffices i subproofs
              |> Theorem.solve s
