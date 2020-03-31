open Support
module B = Beluga
module Context = B.Context
module Command = Beluga.Syntax.Ext.Harpoon
module Id = Beluga.Id
module Total = Beluga.Total
module Whnf = B.Whnf
module F = Misc.Function

module P = B.Pretty.Int.DefaultPrinter

open B.Syntax.Int

let dprintf, dprint, _ = B.Debug.(makeFunctions' (toFlags [11]))
open B.Debug.Fmt

type t = Theorem.t -> Comp.proof_state -> unit

(** Fill the hole with the given closed proof.
    This will solve the current subgoal.
 *)
let solve ?(action_name = "solve") (proof : Comp.proof) : t =
  fun t g -> Theorem.(apply t (Action.make action_name g [] proof))

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
    P.(fmt_ppr_lf_ctyp_decl cD)

type intros'_failure =
  | DuplicateName of LF.mctx * Comp.gctx * Comp.ctyp_decl
  | NothingToIntro

(** Walks a type and collects assumptions into cD and cG,
    returning the conclusion type.

    intros' names cD cG tau = cD' cG' tau'
    such that:
    - cD' is an extension of cD obtained from all the Pi-types in tau;
    - cG' is an extension of cG obtained from all the simple function
      types in tau.

    The given optional names are used for the introduced arguments.
    Else, fresh names are generated internally. User-supplied names
    are used only with computational assumptions, since PiBoxes
    contain a name already. Names supplied by PiBoxes will be
    renumbered to be unique. If a user-supplied name is not unique,
    intros will fail with a DuplicatedNames error
    (see type intros'_failure). This is used by the main intros tactic
    to display an appropriate message.
 *)
let intros' : Theorem.t ->
              string list option -> LF.mctx -> Comp.gctx -> Comp.typ ->
              (intros'_failure, LF.mctx * Comp.gctx * Comp.typ) Either.t =
  let gen_var_for_typ active_names tau =
    B.NameGen.(var tau |> renumber active_names)
  in
  fun t ->
  let rec go updated active_names user_names cD cG tau =
    let next_name = Maybe.(user_names $ Misc.List.uncons) in
    match tau with
    | Comp.TypArr (_, tau_1, tau_2) ->
       let (name, user_names) =
         next_name
         |> Maybe.eliminate
              (fun _ -> gen_var_for_typ active_names tau_1 , None)
              begin fun (name, user_names) ->
              ( B.Id.(mk_name (SomeString name))
              , Some user_names )
              end
       in
       let d = Comp.CTypDecl (name, tau_1, false) in
       begin match check_computational_variable_uniqueness cD cG d t with
       | `unique ->
          go true (name :: active_names) user_names cD (LF.Dec (cG, d))
            tau_2
       | `duplicate -> Either.Left (DuplicateName (cD, cG, d))
       end
    | Comp.TypPiBox (_, (LF.Decl (x, _, _) as d), tau_2) ->
       let x = B.NameGen.renumber active_names x in
       go true (x :: active_names) user_names (LF.Dec (cD, d)) cG tau_2
    | _ when updated -> Either.Right (cD, cG, tau)
    | _ -> Either.Left NothingToIntro
  in
  fun user_names cD cG tau ->
  let active_names =
    Context.(names_of_mctx cD @ names_of_gctx cG)
  in
  go false active_names user_names cD cG tau


(** Introduces all assumptions present in the current goal.
    Solves the input proof state.
 *)
let intros (names : string list option) : t =
  (* Main body of `intros`: *)
  fun t g ->
  let open Comp in
  let (tau, theta) = g.goal in
  match intros' t names LF.Empty LF.Empty tau with
  | Either.Right (cD, cG, tau') ->
     (* only create a new intros node if something actually happened *)
     let goal = (tau', theta) in
     let local_context = {cD; cG; cIH = LF.Empty} in
     let context = Whnf.append_hypotheses g.context local_context in
     let new_state =
       { context
       ; goal
       ; solution = ref None
       ; label = g.label
       }
     in
     (* Solve the current goal with the intros proof. *)
     Theorem.apply_subgoal_replacement t
       "intros"
       new_state
       (Comp.intros context)
       g

  | Either.Left NothingToIntro ->
     Theorem.printf t
       "Nothing to introduce.@,\
        The intros tactic works only when the goal is a function type.@,"

  | Either.Left (DuplicateName (cD, cG, d)) ->
     Theorem.printf t
       "@[<v>Intros failed.\
        @,The generated declaration\
        @,  @[%a@]\
        @,to be added to the computation context\
        @,  @[%a@]\
        @,violates name uniqueness.@]"
       P.(fmt_ppr_cmp_ctyp_decl cD l0) d
       P.(fmt_ppr_cmp_gctx cD l0) cG

let is_valid_goals_for_split_kind k cgs =
  let n = List.length cgs in
  match k with
  | `invert when n <> 1 -> `cant_invert
  | `impossible when n <> 0 -> `not_impossible
  | _ -> `ok

(** Calls the coverage checker to compute the list of goals for a
    given type in the contexts of the given proof state.

    g is a proof state containing cD such that
    - cD |- tau <== type
 *)
let generate_pattern_coverage_goals
      (tau : Comp.typ) (g : Comp.proof_state) t
    : (LF.mctx * (Comp.gctx * Comp.pattern * Comp.tclo) * LF.msub) list =
  let open Comp in
  let names =
    Context.(names_of_mctx g.context.cD @ names_of_gctx g.context.cG)
  in
  B.Coverage.(genPatCGoals names withPatVar g.context.cD (B.Total.strip tau))

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
  let action_name = Fmt.stringify P.fmt_ppr_cmp_split_kind k in
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
     let get_branch (cD, (cG, pat, tau_p), t) =
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
       (* cD_b |- t' : s.context.cD (outside the branch)
          cD_b |- t1' : cD (inside the branch)
          and recall: cD |- t : s.context cD
        *)

       (* cD; cG |- pat <= tau_p
          cD_b; cG_b |- pat' <= [t1']tau_p
          where
          cG_b = [t']s.context.cG, [t1']cG
        *)
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

       (* Compute the gctx inside the branch.*)
       (* cG is given to use by coverage such that
          cD |- cG
          that is, it exists *inside* the branch
        *)
       let cG_p = Whnf.cnormGCtx (cG, t1') in
       let cG_b =
         Context.append
           (Whnf.cnormGCtx (s.context.cG, t'))
           cG_p
       in
       (* cD_b |- cG_b *)
       let cIH_b =
         Whnf.cnormIHCtx (s.context.cIH, t')
       in

       dprintf
         begin fun p ->
         p.fmt "[harpoon-split] @[<v>refined cG and cIH@,\
                cG_b = @[%a@]@,\
                cIH = @[%a@]@,\
                pat' = @[%a@]@]"
           (P.fmt_ppr_cmp_gctx cD_b P.l0) cG_b
           P.(fmt_ppr_cmp_ihctx cD_b cG_b) cIH_b
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
               (P.fmt_ppr_cmp_ihctx cD cG) cIH
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
       let new_state label =
         { context
         ; goal = Pair.rmap (fun s -> Whnf.mcomp s t') s.goal
         ; solution = ref None
         ; label = Comp.SubgoalPath.append s.label label
         }
       in
       (context, t', new_state, (cG_p, pat'))
     in

     let make_context_branch k (context, theta, new_state, (cG_p, pat)) =
       match pat with
       | PatMetaObj (_, (_, LF.CObj cPsi)) ->
          let case_label =
            match cPsi with
            | LF.Null -> EmptyContext Loc.ghost
            | LF.(DDec _) -> ExtendedBy (Loc.ghost, k)
            | _ -> B.Error.violation "[get_context_branch] pattern not a context"
          in
          let label =
            Comp.SubgoalPath.build_context_split i case_label
          in
          let g' = new_state label in
          let p = incomplete_proof Loc.ghost g' in
          ( g'
          , context_branch case_label (cG_p, pat) theta context p
          )
       | _ -> assert false
     in
     let make_meta_branch (context, theta, new_state, (cG_p, pat)) =
       match pat with
       | PatMetaObj (_, (_, LF.ClObj (cPsi, tM))) ->
          let c =
            let LF.(MObj (Root (_, h, _, _))) = tM in
            match h with
            | LF.PVar (n, s) -> `pvar None
            | LF.(Proj (PVar (n, s), k)) -> `pvar (Some k)
            | LF.Const cid -> `ctor cid
            | LF.BVar _ -> `bvar
            | _ ->
               let g = new_state (fun _ -> Comp.SubgoalPath.Here) in
               let Comp.({cD; cG; _}) = g.Comp.context in
               dprintf begin fun p ->
                 p.fmt "[make_meta_branch] @[<v>ERROR\
                        @,tM = @[%a@]@]"
                   P.(fmt_ppr_cmp_pattern cD cG l0) pat
                 end;
               B.Error.violation
                 "[make_meta_branch] head neither pvar (proj) nor const"
          in
          let label = Comp.SubgoalPath.build_meta_split i c in
          let g' = new_state label in
          let p = incomplete_proof Loc.ghost g' in
          ( g'
          , meta_branch c (cG_p, pat) theta context p
          )

       | _ -> B.Error.violation "[make_meta_branch] pattern not a meta object"
     in
     let make_comp_branch (context, theta, new_state, (cG_p, pat)) =
       match pat with
       | PatConst (_, cid, _) ->
          let label =
            Comp.SubgoalPath.build_comp_split i cid
          in
          let g' = new_state label in
          let p = incomplete_proof Loc.ghost g' in
          ( g'
          , comp_branch cid (cG_p, pat) theta context p
          )
       | _ ->
          B.Error.violation "[get_context_branch] pattern not a constant"
     in

     let decide_split_kind =
       function
       | _, (_, PatMetaObj (_, LF.(_, CObj _)), _), _ -> `context
       | _, (_, PatMetaObj (_, LF.(_, ClObj (_, _))), _), _ -> `meta
       | _, (_, PatConst (_, _, _), _), _ -> `comp
       | _ -> B.Error.violation "unhandled pattern type for split"
     in
     match
       List.map decide_split_kind cgs
       |> Nonempty.of_list
       |> Maybe.map Nonempty.all_equal
     with
     | None ->
        let open Theorem in
        impossible_split i
        |> Action.make action_name s []
        |> apply t

     | Some None ->
        B.Error.violation "mixed cases in split (bug in coverage?)"

     | Some (Some k) ->
        let finish f g =
          let f' k cg =
            (* k is the zero-based coverage goal/branch number
               and is used by make_context_branch in order to specify
               the correct schema element index when constructing the
               `extended by k` syntax.
               For a context split,
               goal 0 corresponds to schema element 1
               goal 1 corresponds to schema element 2
               ...
               goal (n-1) corresponds to the last schema element, n.
               goal n corresponds to the empty context case.
               We increment k here so that it exactly equals the
               schema element index
             *)
            f k (get_branch cg)
          in
          List.mapi f' cgs
          |> List.split
          |> Pair.rmap F.(g i tau ++ List.rev)
          |> fun (children, p) ->
             Theorem.(apply t (Action.make action_name s children p))
        in
        match k with
        | `meta -> finish (Misc.const make_meta_branch) Comp.meta_split
        | `comp -> finish (Misc.const make_comp_branch) Comp.comp_split
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
      ; cG = Whnf.cnormGCtx (g.context.cG, shift)
      ; cIH = Whnf.cnormIHCtx (g.context.cIH, shift)
      }
  ; goal = Pair.rmap (fun t -> Whnf.mcomp t shift) g.goal
  ; solution = ref None
  ; label = g.label
  }

let extending_comp_context decl g =
  let open Comp in
  { g with
    context =
      { g.context with
        cG = LF.Dec (g.context.cG, decl)
      }
  ; solution = ref None
  }

(** Solves the current subgoal by keeping it the same, but extending
    the meta context with a new declaration.
    This will appropriately MShift the goal type and the computational
    context.
 *)
let solve_with_new_meta_decl action_name decl f t g =
  let Comp.{cD; _} = Comp.(g.context) in
  match check_metavariable_uniqueness cD decl t with
  | `duplicate -> ()
  | `unique ->
     Theorem.apply_subgoal_replacement t
       action_name
       (extending_meta_context decl g)
       f
       g

(** Solves the current subgoal by keeping it the same, but extending
    the computational context with a new declaration.
 *)
let solve_with_new_comp_decl action_name decl f t g =
  let Comp.{cD; cG; _} = Comp.(g.context) in
  match check_computational_variable_uniqueness cD cG decl t with
  | `duplicate -> ()
  | `unique ->
     Theorem.apply_subgoal_replacement t
       action_name
       (extending_comp_context decl g)
       f
       g

let solve_by_unbox' f (cT : Comp.meta_typ) (name : B.Id.name) : t =
  solve_with_new_meta_decl "unbox" LF.(Decl (name, cT, No)) f

let solve_by_unbox (m : Comp.exp_syn) (mk_cmd : Comp.meta_typ -> Comp.command) (tau : Comp.typ) (name : B.Id.name) modifier : t =
  let open Comp in
  fun t g ->
  let {cD; cG; cIH} = g.context in
     match tau with
     | TypBox (_, cT) ->
        let cT', _ =
          B.Check.Comp.apply_unbox_modifier_opt cD modifier cT
        in
        solve_by_unbox' (prepend_commands [mk_cmd cT]) cT' name t g
     | _ ->
        Theorem.printf t
          "@[<v>The expression@,  @[%a@]@,\
           cannot be unboxed as its type@,  @[%a@]@,is not a box.@]"
          (P.fmt_ppr_cmp_exp_syn cD cG P.l0) m
          (P.fmt_ppr_cmp_typ cD P.l0) tau

let unbox (m : Comp.exp_syn) (tau : Comp.typ) (name : B.Id.name) modifier : t =
  let open Comp in
  solve_by_unbox m (fun cT -> Unbox (m, name, cT, modifier)) tau name modifier

let invoke (i : Comp.exp_syn) (tau : Comp.typ) (name : Id.name) : t =
  let open Comp in
  solve_with_new_comp_decl "by" (CTypDecl (name, tau, false))
    (prepend_commands [By (i, name, tau)])

let suffices (i : Comp.exp_syn) (tau_args : Comp.typ list) (tau_i : Comp.typ) : t =
  fun t g ->
  let open Comp in
  let i_head = head_of_application i in
  let loc = loc_of_exp_syn i in
  let _, (i', ttau_i) =
    B.Check.Comp.genMApp
      loc
      (fun _ -> true)
      g.context.cD
      (i, (tau_i, Whnf.m_id))
  in
  let tau_i' = Whnf.cnormCTyp ttau_i in
  B.Check.Comp.unify_suffices loc g.context.cD tau_i' tau_args
    (Whnf.cnormCTyp g.goal);
  (* generate the subgoals for the arguments.
     by unification it doesn't matter which list we use. *)
  let children, subproofs =
    Misc.Function.flip List.mapi tau_args
      begin fun k tau ->
      let new_state =
        { context = g.context
        ; goal = (tau, Whnf.m_id)
        ; solution = ref None
        ; label =
            Comp.SubgoalPath.(append g.label (build_suffices i_head k))
        }
      in
      (new_state, (Loc.ghost, tau, incomplete_proof Loc.ghost new_state))
      end
    |> List.split
  in
  let p = suffices i' subproofs in
  Theorem.(apply t Action.(make "suffices" g children p))
