open Support

open Beluga
open Beluga_syntax
open Synint

module F = Fun
module E = Error
module S = Substitution
module P = Prettyint.DefaultPrinter
module Indexing_state = Index_state.Indexing_state
module Indexer = Index.Indexer

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

exception No_such_variable of Name.t * [ `meta | `comp ]

exception Prover_error of exn

let throw e = Error.raise (Prover_error e)

let () =
  Error.register_exception_printer (function
    | No_such_variable (name, `meta) ->
      Format.dprintf "No such metavariable %a." Name.pp name
    | No_such_variable (name, `comp) ->
      Format.dprintf "No such computational variable %a." Name.pp name
    | Prover_error e -> Error.find_printer e
    | exn -> Error.raise_unsupported_exception_printing exn)

(** Elaborates a synthesizable expression in the given contexts. *)
let elaborate_synthesizing_expression state mcid cIH cD cG mfs t =
  let (hs, (i, tau)) =
    Holes.catch
      begin fun () ->
      let (i, (tau, theta)) =
        let apx_exp =
          Indexing_state.with_bindings_checkpoint state (fun state ->
              Indexing_state.add_all_mctx state cD;
              Indexing_state.add_all_gctx state cG;
              Indexer.index_comp_expression state t)
        in
        (* FIXME: The following elaboration step needs a checkpoint *)
        Reconstruct.elExp' cD cG apx_exp
      in
      dprintf
        begin fun p ->
        p.fmt "[%s] @[<v>done:@,\
                i = @[%a@] (internal)@]"
          __FUNCTION__
          P.(fmt_ppr_cmp_exp cD cG l0) i
        end;
      let i' = Whnf.cnormExp (i, Whnf.m_id) in
      let _ = Check.Comp.syn mcid ~cIH: cIH cD cG mfs i' in  (* (tau, theta); *)
      (i', Whnf.cnormCTyp (tau, theta))
      end
  in
  (hs, i, tau)

(** Elaborates a checkable expression in the given contexts against the given type. *)
let elaborate_checkable_expression state mcid cIH cD cG mfs t ttau =
  Holes.catch
    begin fun () ->
    let ttau' = Pair.map_left Total.strip ttau in
    let e =
      let apx_exp =
        Indexing_state.with_bindings_checkpoint state (fun state ->
            Indexing_state.add_all_mctx state cD;
            Indexing_state.add_all_gctx state cG;
            Indexer.index_comp_expression state t)
      in
      (* FIXME: The following elaboration step needs a checkpoint *)
      Reconstruct.elExp cD cG apx_exp ttau'
    in
    let e' = Whnf.cnormExp (e, Whnf.m_id) in
    Check.Comp.check mcid ~cIH: cIH cD cG mfs e' ttau;
    e'
    end

let elaborate_typ state cD tau =
  let (tau, _k) =
    let apx_tau =
        Indexing_state.with_bindings_checkpoint state (fun state ->
            Indexing_state.add_all_mctx state cD;
            Indexer.index_open_comp_typ state tau)
      in
      (* FIXME: The following elaboration steps need checkpoints *)
      apx_tau
      |> Reconstruct.comptyp_cD cD
      |> Abstract.comptyp
      |> Pair.map_left (fun tau -> Whnf.cnormCTyp (tau, Whnf.m_id))
      |> F.through (fun (tau, _) -> Check.Comp.checkTyp cD tau)
  in
  tau

(** Elaborates a metavariable. *)
let elaborate_mvar state cD loc name =
  (* This is kind of sketchy since we don't parse a head, but rather
      just a name (or a hash_name), and we do all the elaboration "by
      hand" here instead of using Lfrecon and Index.
    *)
  let p (d, _) = Name.(LF.name_of_ctyp_decl d = name) in
  match Context.find_with_index_rev' cD p with
  | None -> Lfrecon.(throw loc (UnboundName name))
  | Some LF.(Decl (_, cT, _, _), k) ->
      let cT = Whnf.cnormMTyp (cT, LF.MShift k) in
      dprintf
        begin fun p ->
        p.fmt "[%s] @[<v>found index %d for metavariable@,\
              @[<hov 2>%a :@ @[%a@]@]@]"
          __FUNCTION__
          k
          Name.pp name
          P.(fmt_ppr_cmp_meta_typ cD) cT
        end;
      let mF =
        let open LF in
        match cT with
        | ClTyp (mT, cPsi) ->
          let psi_hat = Context.dctxToHat cPsi in
          let obj =
            match mT with
            | MTyp _ -> MObj (MVar (Offset k, S.LF.id) |> head)
            | PTyp _ -> PObj (PVar (k, S.LF.id))
            | STyp _ -> SObj (SVar (k, 0, S.LF.id)) (* FIXME: not sure about 0 -je *)
          in
          ClObj (psi_hat, obj)
        | LF.CTyp _ ->
          let cPsi = LF.(CtxVar (CtxOffset k)) in
          CObj cPsi
      in
      let i = Comp.AnnBox (Location.ghost, (loc, mF), cT)
      and tau = Comp.TypBox (loc, cT) in
      (i, tau)
  | _ -> E.raise_violation
          (Format.asprintf "[%s] cD decl has no type" __FUNCTION__)


let dump_proof t path =
  Out_channel.with_open_bin path (fun out_channel ->
    let ppf = Format.formatter_of_out_channel out_channel in
    Theorem.dump_proof ppf t;
    Format.pp_print_newline ppf ())

let process_command
      ((index_state),
      (s : HarpoonState.t),
      ({ HarpoonState.session = c; theorem = t; proof_state = g } as substate))
      (cmd : Synext.harpoon_repl_command)
    : unit =
  let open Comp in

  let solve_hole (id, Holes.Exists (w, h)) =
    let open Holes in
    dprintf
      begin fun p ->
      p.fmt "[harpoon] [solve_hole] processing hole %s"
        (HoleId.string_of_name_or_id (h.Holes.name, id))
      end;
    let { name; Holes.cD = cDh; info; _ } = h in
    match w with
    | Holes.CompInfo ->
      begin
        let { compGoal; Holes.cG = cGh; compSolution } = h.info
        in
        assert (compSolution = None);
        let typ = Whnf.cnormCTyp compGoal in
        dprintf
          begin fun p ->
          p.fmt "[%s] @[<v>goal: @[%a@]@]"
            __FUNCTION__
            (P.fmt_ppr_cmp_typ cDh P.l0) typ
          end;
        Logic.prepare ();
        let (mquery, skinnyCTyp, mquerySub, instMMVars) =
          let (typ', k) = Abstract.comptyp typ in
          Logic.Convert.comptypToMQuery (typ', k)
        in
        let mfs = Session.get_mutual_decs c in
        let maximum_search_depth = Option.some 999 in
        let induction_argument_index = Option.none in
        let maximum_split_depth = 2 in
        let thm_cid = Option.none in
        try
          Logic.CSolver.cgSolve cDh cGh LF.Empty mquery
            begin
              fun e ->
                HarpoonState.printf s "found solution: @[%a@]@,@?"
                (P.fmt_ppr_cmp_exp cDh cGh P.l0) e;
              h.info.compSolution <- Some e;
              raise Logic.Frontend.Done
            end
            (maximum_search_depth, induction_argument_index, maximum_split_depth)
            (skinnyCTyp, thm_cid, mfs)
        with
          | Logic.Frontend.Done ->
            HarpoonState.printf s "logic programming finished@,@?"
      end
    | Holes.LFInfo ->
       let { lfGoal; cPsi; lfSolution } = h.info in
       assert (lfSolution = None);
       let typ = Whnf.normTyp lfGoal in
       dprintf
         begin fun p ->
         p.fmt "[%s] @[<v>goal: @[%a@]@]"
           __FUNCTION__
           (P.fmt_ppr_lf_typ cDh cPsi P.l0) typ
         end;
       Logic.prepare ();
       let (query, skinnyTyp, querySub, instMVars) =
         Logic.Convert.typToQuery cDh cPsi (typ, 0)
       in
       try
         Logic.Solver.solve cDh cPsi query
           begin fun (cPsi, tM) ->
           HarpoonState.printf s "found solution: @[%a@]@,@?"
             (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
           h.info.lfSolution <- Some (tM, LF.Shift 0);
           raise Logic.Frontend.Done
           end
           (Some 100)
       with
       | Logic.Frontend.Done ->
          HarpoonState.printf s "logic programming finished@,@?"
  in

  let { cD; cG; cIH } = g.context in

  match cmd with
  (* Administrative commands: *)
  | Synext.Harpoon.Repl.Command.Theorem { subcommand = cmd; _ } ->
     begin match cmd with
     | `list ->
        HarpoonState.printf s "@[<v>%a@,@,Current theorem is first.@]"
          Session.fmt_ppr_theorem_list c
     | `defer -> Session.defer_theorem c
     | `show_ihs ->
        let f i =
          HarpoonState.printf s "%d. @[%a@]@,"
            (i + 1)
            (P.fmt_ppr_cmp_ih g.context.cD g.context.cG)
        in
        HarpoonState.printf s "@[<v>There are %d IHs:@,"
          (Context.length g.context.cIH);
        Context.to_list g.context.cIH |> List.iteri f;
        HarpoonState.printf s "@]"
     | `dump_proof path ->
        dump_proof t path
     | `show_proof ->
        Theorem.show_proof t
     end

  | Synext.Harpoon.Repl.Command.Session { subcommand = cmd; _ } ->
     begin match cmd with
     | `list ->
        HarpoonState.printf s "@[<v>%a@,@,Current session and theorem are first.@]"
          HarpoonState.fmt_ppr_session_list s
     | `defer -> HarpoonState.defer_session s
     | `create -> ignore (HarpoonState.session_configuration_wizard s)
     | `serialize -> HarpoonState.serialize s substate
     end

  | Synext.Harpoon.Repl.Command.Subgoal { subcommand = cmd; _ } ->
     begin match cmd with
     | `list -> Theorem.show_subgoals t
     | `defer -> Theorem.defer_subgoal t
     end

  | Synext.Harpoon.Repl.Command.Select_theorem { theorem; _ } ->
     let name = Name.make_from_qualified_identifier theorem in
     if Bool.not (HarpoonState.select_theorem s name) then
       HarpoonState.printf s
         "There is no theorem by name %a."
         Name.pp name

  | Synext.Harpoon.Repl.Command.Rename
    { rename_from = rename_from, _rename_from_modifier
    ; rename_to = rename_to, _rename_to_modifier
    ; level
    ; _ } ->
     let x_src = Name.make_from_identifier rename_from
     and x_dst = Name.make_from_identifier rename_to in
     if Bool.not (Theorem.rename_variable x_src x_dst level t g) then
       throw (No_such_variable (x_src, level))

  | Synext.Harpoon.Repl.Command.Toggle_automation { kind; change; _ } ->
     Automation.toggle
       (HarpoonState.automation_state s)
       kind
       change

  | Synext.Harpoon.Repl.Command.Type { scrutinee; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, i, tau) =
       elaborate_synthesizing_expression index_state (Some cid)
         cIH cD cG mfs scrutinee
     in
     HarpoonState.printf s
       "- @[<hov 2>@[%a@] :@ @[%a@]@]"
       (P.fmt_ppr_cmp_exp cD cG P.l0) i
       (P.fmt_ppr_cmp_typ cD P.l0) tau

  | Synext.Harpoon.Repl.Command.Info { kind; object_identifier; _ } ->
     begin match kind with
     | `prog ->
        let cid = Indexing_state.index_of_comp_program index_state object_identifier in
        let e = Store.Cid.Comp.get cid in
        HarpoonState.printf s
          "- @[%a@]"
          P.fmt_ppr_cmp_comp_prog_info e
     end

  | Synext.Harpoon.Repl.Command.Translate { theorem; _ } ->
     let cid = Indexing_state.index_of_comp_program index_state theorem in
     let e = Store.Cid.Comp.get cid in
     HarpoonState.printf s "%a"
       Translate.fmt_ppr_result (Translate.entry e)

  | Synext.Harpoon.Repl.Command.Undo _ ->
     if Bool.not (Theorem.history_step_backward t) then
       HarpoonState.printf s "Nothing to undo in the current theorem's timeline."

  | Synext.Harpoon.Repl.Command.Redo _ ->
     if Bool.not (Theorem.history_step_forward t) then
       HarpoonState.printf s "Nothing to redo in the current theorem's timeline."

  | Synext.Harpoon.Repl.Command.History _ ->
     let (past, future) = Theorem.get_history_names t in
     let future = List.rev future in
     let line ppf = function
       | _ when List.nonempty future ->
          Format.fprintf ppf "@,-----@,"
       | _ -> ()
     in
     let future_remark ppf = function
       | _ when List.nonempty future ->
          Format.fprintf ppf "- @[%a@]"
            Format.pp_print_string
            "Commands below the line would be undone. \
             Commands above the line would be redone."
       | _ -> ()
     in
     HarpoonState.printf s
       "@[<v 2>History:\
        @,@[<v>%a@]%a@[<v>%a@]@]@,%a@,"
       (Format.pp_print_list ~pp_sep:Format.pp_print_cut Format.pp_print_string)
       future
       line ()
       (Format.pp_print_list ~pp_sep:Format.pp_print_cut Format.pp_print_string)
       past
       future_remark ()

  | Synext.Harpoon.Repl.Command.Help _ ->
     HarpoonState.printf s
       "@[<v>Built-in help is not implemented.\
        @,See online documentation: https://beluga-lang.readthedocs.io/@]"

  (* Real tactics: *)
  | Synext.Harpoon.Repl.Command.Unbox
    { expression
    ; assignee = assignee, _modifier
    ; modifier; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, m, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs expression
     in
     let name = Name.make_from_identifier assignee in
     Tactic.unbox m tau name modifier t g

  | Synext.Harpoon.Repl.Command.Intros { introduced_variables; _ } ->
     let names =
       Option.map Fun.(List1.map Identifier.show >> List1.to_list) introduced_variables
     in
     Tactic.intros names t g

  | Synext.Harpoon.Repl.Command.Split { location; scrutinee; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, m, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs scrutinee
     in
     Tactic.split `split m tau mfs t g

  | Synext.Harpoon.Repl.Command.Invert { location; scrutinee; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, m, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs scrutinee
     in
     Tactic.split `invert m tau mfs t g

  | Synext.Harpoon.Repl.Command.Impossible { location; scrutinee; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, m, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs scrutinee
     in
     Tactic.split `impossible m tau mfs t g

  | Synext.Harpoon.Repl.Command.Msplit { location; identifier } ->
     let name = Name.make_from_identifier identifier in
     let i, tau = elaborate_mvar index_state cD location name in
     let mfs = Session.get_mutual_decs c in
     Tactic.split `split i tau mfs t g

  | Synext.Harpoon.Repl.Command.By { expression; assignee; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, i, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs expression
     in
     let name = Name.make_from_identifier assignee in
     dprintf
       begin fun p ->
       p.fmt "@[<v>[harpoon-By] elaborated invocation:@,%a@ : %a@]"
         (P.fmt_ppr_cmp_exp cD cG P.l0) i
         (P.fmt_ppr_cmp_typ cD P.l0) tau
       end;
     if Whnf.closedExp i then
       (List.iter solve_hole hs; Tactic.invoke i tau name t g)
     else
       HarpoonState.printf s
         "@[<v>Elaborated expression\
          @,  @[%a@]\
          @,of type\
          @,  @[%a@]\
          @,is not closed.\
          @,Both the expression and its type must be closed for use with `by`.@]"
         (P.fmt_ppr_cmp_exp cD cG P.l0) i
         (P.fmt_ppr_cmp_typ cD P.l0) tau

  | Synext.Harpoon.Repl.Command.Suffices { implication; goal_premises; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, i, tau) =
       elaborate_synthesizing_expression index_state (Some cid) cIH cD cG mfs implication
     in
     begin match Session.infer_invocation_kind c i with
     | `ih ->
        HarpoonState.printf s "inductive use of `suffices by ...` is not currently supported"
     | `lemma ->
        begin match hs with
        | _ :: _ ->
           Theorem.printf t "holes are not supported for `suffices by _ ...`"
        | [] ->
           let elab_suffices_typ tau_ext : suffices_typ =
             map_suffices_typ (fun typ -> elaborate_typ index_state cD typ) tau_ext
           in
           let tau_list = List.map elab_suffices_typ goal_premises in
           Tactic.suffices i tau_list tau t g
        end
     end

  | Synext.Harpoon.Repl.Command.Solve { solution = e; _ } ->
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let (hs, e) =
       elaborate_checkable_expression index_state (Some cid) cIH cD cG mfs e g.goal
     in
     dprnt "[harpoon] [solve] elaboration finished";
     (* State.printf s "Found %d hole(s) in solution@\n" (List.length hs); *)
     List.iter solve_hole hs;
     dprnt "[harpoon] [solve] double-check!";
     Check.Comp.check (Some cid) cD cG mfs ~cIH: cIH e g.goal;
     dprnt "[harpoon] [solve] double-check DONE";
     let e = Whnf.cnormExp (e, Whnf.m_id) in
     if Whnf.closedExp e then
       (Comp.solve e |> Tactic.solve) t g
     else
       HarpoonState.printf s "Solution contains uninstantiated metavariables."

  | Synext.Harpoon.Repl.Command.Auto_invert_solve { max_depth = d; _ } ->
     let { cD; cG; cIH } = g.context in
     let (tau, ms) = g.goal in
     let tau = Whnf.cnormCTyp (tau, ms) in
     let (mquery, _, _, instMMVars) =
       let (typ',k) = Abstract.comptyp tau in
       Logic.Convert.comptypToMQuery (typ',k)
     in
     let (theorem, _) = Theorem.get_statement t in
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let opt_witness = Logic.Frontend.msolve_tactic (cD, cG, cIH)
                         (mquery, tau, instMMVars) d
                         (theorem, cid, 1, mfs)
     in
     begin
     match opt_witness with
     | None ->
         HarpoonState.printf s "cgSolve cannot find a proof in cD = %a, cG = %a, skinny = %a, inst size = %d."
         P.(fmt_ppr_lf_mctx l0) cD
         P.(fmt_ppr_cmp_gctx cD l0) cG
         P.(fmt_ppr_cmp_typ cD l0) tau
         (List.length(instMMVars))
     | Some e ->
        (Comp.solve e |> Tactic.solve) t g
     end

  | Synext.Harpoon.Repl.Command.Inductive_auto_solve { max_depth = d; _ } ->
     let { cD; cG; cIH } = g.context in
     let (tau, ms) = g.goal in
     let tau = Whnf.cnormCTyp (tau, ms) in
     let (mquery, _, _, instMMVars) =
       let (typ',k) = Abstract.comptyp tau in
       Logic.Convert.comptypToMQuery (typ',k)
     in
     let (theorem, _) = Theorem.get_statement t in
     let cid = Theorem.get_cid t in
     let mfs = Session.get_mutual_decs c in
     let opt_witness = Logic.Frontend.msolve_tactic (cD, cG, cIH)
                         (mquery, tau, instMMVars) d
                         (theorem, cid, 2, mfs)
     in
     begin
     match opt_witness with
     | None ->
         HarpoonState.printf s "cgSolve cannot find a proof in cD = %a, cG = %a, skinny = %a, inst size = %d."
         P.(fmt_ppr_lf_mctx l0) cD
         P.(fmt_ppr_cmp_gctx cD l0) cG
         P.(fmt_ppr_cmp_typ cD l0) tau
         (List.length(instMMVars))
     | Some e ->
        (Comp.solve e |> Tactic.solve) t g
     end
