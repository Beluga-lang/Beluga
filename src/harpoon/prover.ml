open Support

open Beluga
open Syntax.Int

module E = Beluga_syntax.Error
module Command = Syntax.Ext.Harpoon
module S = Substitution
module P = Pretty.Int.DefaultPrinter
module CompS = Store.Cid.Comp

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

module Error = struct
  type t =
    | NoSuchVariable of Name.t * [ `meta | `comp ]

  exception E of t

  let throw e = raise (E e)

  let error_printer = function
    | NoSuchVariable (name, level) ->
       let format_variable_kind ppf = function
         | `meta -> Format.fprintf ppf "metavariable"
         | `comp -> Format.fprintf ppf "computational variable"
       in
       Format.dprintf "No such %a %a."
         format_variable_kind level
         Name.pp name

  let () =
    Beluga_syntax.Error.register_exception_printer (function
      | E e -> error_printer e
      | exn -> Beluga_syntax.Error.raise_unsupported_exception_printing exn)
end

(** High-level elaboration from external to internal syntax. *)
module Elab = struct
  (** Elaborates a synthesizable expression in the given contexts. *)
  let exp' mcid cIH cD cG mfs t =
    let (hs, (i, tau)) =
      Holes.catch
        begin fun _ ->
        let (i, (tau, theta)) =
          Interactive.elaborate_exp' cD cG t
        in
        dprintf
          begin fun p ->
          p.fmt "[elaborate_exp'] @[<v>done:@,\
                 i = @[%a@] (internal)@]"
            P.(fmt_ppr_cmp_exp cD cG l0) i
          end;
        let i = Whnf.cnormExp (i, Whnf.m_id) in
        let _ = Check.Comp.syn mcid ~cIH: cIH cD cG mfs i in  (* (tau, theta); *)
        (i, Whnf.cnormCTyp (tau, theta))
        end
    in
    (hs, i, tau)

  (** Elaborates a checkable expression in the given contexts against the given type. *)
  let exp mcid cIH cD cG mfs t ttau =
    Holes.catch
      begin fun _ ->
      let e = Interactive.elaborate_exp cD cG t (Pair.map_left Total.strip ttau) in
      let e = Whnf.cnormExp (e, Whnf.m_id) in
      Check.Comp.check mcid ~cIH: cIH cD cG mfs e ttau;
      e
      end

  let typ cD tau =
    let (tau, k) = Interactive.elaborate_typ cD tau in
    tau

  (** Elaborates a metavariable. *)
  let mvar cD loc name =
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
         p.fmt "[harpoon] [Elab.mvar] @[<v>found index %d for metavariable@,\
                @[<hov 2>%a :@ @[%a@]@]@]"
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
              | STyp _ -> SObj (SVar (k, 0, S.LF.id)) (* XXX not sure about 0 -je *)
            in
            ClObj (psi_hat, obj)
         | LF.CTyp _ ->
            let cPsi = LF.(CtxVar (CtxOffset k)) in
            CObj cPsi
       in
       let i = Comp.AnnBox (Beluga_syntax.Location.ghost, (loc, mF), cT)
       and tau = Comp.TypBox (loc, cT) in
       (i, tau)
    | _ -> E.violation "[harpoon] [Elab] [mvar] cD decl has no type"

end

(*
  (** Removes the theorem with a given name from the list of theorems. *)
  let remove_theorem s name =
    let n = DynArray.length s.theorems in
    let rec loop = function
      | i when i >= n -> ()
      | i when Name.equal name (DynArray.get s.theorems i).Theorem.name ->
         DynArray.delete s.theorems i
      | i -> loop (i + 1)
    in
    loop 0
 *)

let dump_proof t path =
  let out = open_out path in
  let ppf = Format.formatter_of_out_channel out in
  Theorem.dump_proof ppf t;
  Format.pp_print_newline ppf ();
  close_out out

let process_command
      (s : HarpoonState.t)
      ( (c, t, g) : HarpoonState.triple)
      (cmd : Command.command)
    : unit =
  let mfs =
    lazy
      begin
        let ds = Session.get_mutual_decs c in
        dprintf
          begin fun p ->
          p.fmt "[harpoon] [mfs] @[<v>got mutual decs:\
                 @,-> @[<v>%a@]@]"
            (Format.pp_print_list ~pp_sep: Format.pp_print_cut
               P.fmt_ppr_cmp_total_dec)
            ds
          end;
        ds
      end
  in

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
          p.fmt "[harpoon] [solve] [holes] @[<v>goal: @[%a@]@]"
            (P.fmt_ppr_cmp_typ cDh Pretty.Int.DefaultPrinter.l0) typ
          end;
        Logic.prepare ();
        let (mquery, skinnyCTyp, mquerySub, instMMVars) =
          let (typ', k) = Abstract.comptyp typ in
          Logic.Convert.comptypToMQuery (typ', k)
        in
        try
          Logic.CSolver.cgSolve cDh cGh LF.Empty mquery
            begin
              fun e ->
                HarpoonState.printf s "found solution: @[%a@]@,@?"
                (P.fmt_ppr_cmp_exp cDh cGh P.l0) e;
              h.info.compSolution <- Some e;
              raise Logic.Frontend.Done
            end
            (Some 999, None, 2) (skinnyCTyp, None, Lazy.force mfs)
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
         p.fmt "[harpoon] [solve] [holes] @[<v>goal: @[%a@]@]"
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
  | Command.Theorem cmd ->
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
  | Command.Session cmd ->
     begin match cmd with
     | `list ->
        HarpoonState.printf s "@[<v>%a@,@,Current session and theorem are first.@]"
          HarpoonState.fmt_ppr_session_list s
     | `defer -> HarpoonState.defer_session s
     | `create -> ignore (HarpoonState.session_configuration_wizard s)
     | `serialize -> HarpoonState.serialize s (c, t, g)
     end
  | Command.Subgoal cmd ->
     begin match cmd with
     | `list -> Theorem.show_subgoals t
     | `defer -> Theorem.defer_subgoal t
     end

  | Command.SelectTheorem name ->
     if Bool.not (HarpoonState.select_theorem s name) then
       HarpoonState.printf s
         "There is no theorem by name %a."
         Name.pp name

  | Command.Rename { rename_from=x_src; rename_to=x_dst; level } ->
     if Bool.not (Theorem.rename_variable x_src x_dst level t g) then
       Error.(throw (NoSuchVariable (x_src, level)))

  | Command.ToggleAutomation (automation_kind, automation_change) ->
     Automation.toggle
       (HarpoonState.automation_state s)
       automation_kind
       automation_change

  | Command.Type i ->
     let (hs, i, tau) =
       Elab.exp' (Some (Theorem.get_cid t))
         cIH cD cG (Lazy.force mfs) i
     in
     HarpoonState.printf s
       "- @[<hov 2>@[%a@] :@ @[%a@]@]"
       (P.fmt_ppr_cmp_exp cD cG P.l0) i
       (P.fmt_ppr_cmp_typ cD P.l0) tau

  | Command.Info (k, n) ->
     begin match k with
     | `prog ->
        let open Option in
        begin match CompS.(index_of_name_opt n $> get) with
        | None ->
           HarpoonState.printf s
             "- No such theorem by name %a" Name.pp n
        | Some e ->
           HarpoonState.printf s
             "- @[%a@]"
             P.fmt_ppr_cmp_comp_prog_info e
        end
     end

  | Command.Translate n ->
     let open Option in
     begin match CompS.(index_of_name_opt n $> get) with
     | Some e ->
        HarpoonState.printf s "%a"
          Translate.fmt_ppr_result (Translate.entry e)
     | None ->
        HarpoonState.printf s "No such theorem by name %a defined."
          Name.pp n
     end

  | Command.Undo ->
     if Bool.not Theorem.(history_step t Direction.backward) then
       HarpoonState.printf s "Nothing to undo in the current theorem's timeline."

  | Command.Redo ->
     if Bool.not Theorem.(history_step t Direction.forward) then
       HarpoonState.printf s "Nothing to redo in the current theorem's timeline."

  | Command.History ->
     let open Format in
     let (past, future) = Theorem.get_history_names t in
     let future = List.rev future in
     let line ppf = function
       | _ when List.nonempty future ->
          fprintf ppf "@,-----@,"
       | _ -> ()
     in
     let future_remark ppf = function
       | _ when List.nonempty future ->
          fprintf ppf "- @[%a@]"
            pp_print_string
            "Commands below the line would be undone. \
             Commands above the line would be redone."
       | _ -> ()
     in
     HarpoonState.printf s
       "@[<v 2>History:\
        @,@[<v>%a@]%a@[<v>%a@]@]@,%a@,"
       (pp_print_list ~pp_sep: pp_print_cut pp_print_string)
       future
       line ()
       (pp_print_list ~pp_sep: pp_print_cut pp_print_string)
       past
       future_remark ()

  | Command.Help ->
     HarpoonState.printf s
       "@[<v>Built-in help is not implemented.\
        @,See online documentation: https://beluga-lang.readthedocs.io/@]"

  (* Real tactics: *)
  | Command.Unbox (i, name, modifier) ->
     let (hs, m, tau) =
       let cid = Theorem.get_cid t in
       Elab.exp' (Some cid) cIH cD cG (Lazy.force mfs) i
     in
     Tactic.unbox m tau name modifier t g

  | Command.Intros names ->
     Tactic.intros names t g

  | Command.Split (split_kind, i) ->
     let (hs, m, tau) =
       let cid = Theorem.get_cid t in
       Elab.exp' (Some cid) cIH cD cG (Lazy.force mfs) i
     in
     Tactic.split split_kind m tau (Lazy.force mfs) t g
  | Command.MSplit (loc, name) ->
     let i, tau = Elab.mvar cD loc name in
     Tactic.split `split i tau (Lazy.force mfs) t g
  | Command.By (i, name) ->
     let (hs, i, tau) =
       let cid = Theorem.get_cid t in
       Elab.exp' (Some cid) cIH cD cG (Lazy.force mfs) i
     in
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

  | Command.Suffices (i, tau_list) ->
     let (hs, i, tau) =
       let cid = Theorem.get_cid t in
       Elab.exp' (Some cid) cIH cD cG (Lazy.force mfs) i
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
             map_suffices_typ (Elab.typ cD) tau_ext
           in
           let tau_list = List.map elab_suffices_typ tau_list in
           Tactic.suffices i tau_list tau t g
        end
     end

  | Command.Solve e ->
     let cid = Theorem.get_cid t in
     let (hs, e) =
       Elab.exp (Some cid) cIH cD cG (Lazy.force mfs) e g.goal
     in
     dprnt "[harpoon] [solve] elaboration finished";
     (* State.printf s "Found %d hole(s) in solution@." (List.length hs); *)
     List.iter solve_hole hs;
     dprnt "[harpoon] [solve] double-check!";
     Check.Comp.check (Some cid) cD cG (Lazy.force mfs) ~cIH: cIH e g.goal;
     dprnt "[harpoon] [solve] double-check DONE";
     let e = Whnf.cnormExp (e, Whnf.m_id) in
     if Whnf.closedExp e then
       (Comp.solve e |> Tactic.solve) t g
     else
       HarpoonState.printf s "Solution contains uninstantiated metavariables."
  | Command.AutoInvertSolve d ->
     let { cD; cG; cIH } = g.context in
     let (tau, ms) = g.goal in
     let tau = Whnf.cnormCTyp (tau, ms) in
     let (mquery, _, _, instMMVars) =
       let (typ',k) = Abstract.comptyp tau in
       Logic.Convert.comptypToMQuery (typ',k)
     in
     let (theorem, _) = Theorem.get_statement t in
     let cid = Theorem.get_cid t in
     let opt_witness = Logic.Frontend.msolve_tactic (cD, cG, cIH)
                         (mquery, tau, instMMVars) d
                         (theorem, cid, 1, (Lazy.force mfs))
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

  | Command.InductiveAutoSolve d ->
     let { cD; cG; cIH } = g.context in
     let (tau, ms) = g.goal in
     let tau = Whnf.cnormCTyp (tau, ms) in
     let (mquery, _, _, instMMVars) =
       let (typ',k) = Abstract.comptyp tau in
       Logic.Convert.comptypToMQuery (typ',k)
     in
     let (theorem, _) = Theorem.get_statement t in
     let cid = Theorem.get_cid t in
     let opt_witness = Logic.Frontend.msolve_tactic (cD, cG, cIH)
                         (mquery, tau, instMMVars) d
                         (theorem, cid, 2, (Lazy.force mfs))
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
