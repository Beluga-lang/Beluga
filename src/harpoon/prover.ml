open Support

module B = Beluga
module Check = B.Check
module Command = B.Syntax.Ext.Harpoon
module Context = B.Context
module Comp = B.Syntax.Int.Comp
module HoleId = B.HoleId
module Holes = B.Holes
module Id = B.Id
module Interactive = B.Interactive
module LF = B.Syntax.Int.LF
module Logic = B.Logic
module P = B.Pretty.Int.DefaultPrinter
module Total = B.Total
module Whnf = B.Whnf
module S = B.Substitution
module Debug = B.Debug
module F = Misc.Function
module CompS = B.Store.Cid.Comp
module Loc = B.Location

let dprintf, _, dprnt = Debug.(makeFunctions' (toFlags [13]))
open Debug.Fmt

exception EndOfInput

let _ =
  B.Error.register_printer
    begin fun EndOfInput ->
    B.Error.print
      begin fun ppf ->
      Format.fprintf ppf "End of input."
      end
    end

(** High-level elaboration from external to internal syntax. *)
module Elab = struct
  (** Elaborates a synthesizable expression in the given contexts. *)
  let exp' cIH cD cG mfs t =
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
            P.(fmt_ppr_cmp_exp_syn cD cG l0) i
          end;
        let i = Whnf.(cnormExp' (i, m_id)) in
        let _ = Check.Comp.syn ~cIH: cIH cD cG mfs i in  (* (tau, theta); *)
        (i, Whnf.cnormCTyp (tau, theta))
        end
    in
    (hs, i, tau)

  (** Elaborates a checkable expression in the given contexts against the given type. *)
  let exp cIH cD cG mfs t ttau =
    Holes.catch
      begin fun _ ->
      let e = Interactive.elaborate_exp cD cG t (Pair.lmap Total.strip ttau) in
      let e = Whnf.(cnormExp (e, m_id)) in
      Check.Comp.check ~cIH: cIH cD cG mfs e ttau;
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
    let p (d, _) = Id.equals name (LF.name_of_ctyp_decl d) in
    match Context.find_with_index_rev' cD p with
    | None -> B.Lfrecon.(throw loc (UnboundName name))
    | Some LF.(Decl (_, cT, dep), k) ->
       let cT = Whnf.cnormMTyp (cT, LF.MShift k) in
       dprintf
         begin fun p ->
         p.fmt "[harpoon] [Elab.mvar] @[<v>found index %d for metavariable@,\
                @[<hov 2>%a :@ @[%a@]@]@]"
           k
           Id.print name
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
       let i =
         Comp.AnnBox ( (loc, mF), cT )
       in
       let tau =
         Comp.TypBox (loc, cT)
       in
       (i, tau)
    | _ -> B.Error.violation "[harpoon] [Elab] [mvar] cD decl has no type"

end

(**
 * TODO: Move this util into a dedicated module
 * TODO: Add more abstraction layers for system level operations
 *)
let replace_locs (replacees : (Loc.t * (Format.formatter -> unit -> unit)) list) : unit =
  replacees
  |> Misc.Hashtbl.group_by
       begin fun (loc, _) ->
       Loc.filename loc
       end
  (* iterate over replacee groups
   (* open file stream *)
   (* sort items in the group *)
   (* iterate over the items
   (* iterate over file stream and print uchars until it meets the item hole *)
   (* print the item value *)
   *)
   *)
  |> Hashtbl.iter
       begin fun (file_name : string) replacees ->
       let in_ch = open_in file_name in
       let in_lexbuf = Sedlexing.Utf8.from_channel in_ch in
       let read_length = ref 0 in
       let indentation = ref 0 in
       let raise_edited_error () =
         B.Error.violation "[harpoon] [serialize] original file is edited"
       in
       let with_uchar n f =
         match Sedlexing.next in_lexbuf with
         | None -> n ()
         | Some v ->
            incr read_length;
            begin
              if v != Uchar.of_char '\n'
              then incr indentation
              else indentation := 0
            end;
            f v
       in
       let (temp_file_name, out_ch) = Filename.open_temp_file "beluga_harpoon" "" in
       try
         let outbuf = Buffer.create 4 in
         replacees
         |> List.sort (Misc.on fst Loc.compare_start)
         |> List.iter
              begin fun (loc, printer) ->
              let start_offset = Loc.start_offset loc in
              let stop_offset = Loc.stop_offset loc in
              Misc.Function.until
                begin fun _ ->
                if !read_length < start_offset
                then
                  with_uchar raise_edited_error
                    begin fun v ->
                    Buffer.clear outbuf;
                    Buffer.add_utf_8_uchar outbuf v;
                    Buffer.output_buffer out_ch outbuf;
                    true
                    end
                else
                  false
                end;
              let ppf = Format.formatter_of_out_channel out_ch in
              Format.pp_open_vbox ppf !indentation;
              printer ppf ();
              Format.pp_close_box ppf ();
              Format.pp_print_flush ppf ();
              Misc.Function.until
                begin fun _ ->
                if !read_length < stop_offset
                then
                  with_uchar raise_edited_error (Misc.const true)
                else
                  false
                end
              end;
         Misc.Function.until
           begin fun _ ->
           with_uchar (Misc.const false)
             begin fun v ->
             Buffer.clear outbuf;
             Buffer.add_utf_8_uchar outbuf v;
             Buffer.output_buffer out_ch outbuf;
             true
             end
           end;
         flush out_ch;
         Sys.rename temp_file_name file_name
       with
       | e ->
          close_in in_ch;
          close_out out_ch;
          Sys.remove temp_file_name
       end

let update_existing_holes existing_holes =
  let open Maybe in
  existing_holes
  |> List.map (fun (loc, (_, ps)) -> (loc, ps))
  |> filter_map
       begin fun (loc, ps) ->
       let open Comp in
       !(ps.solution)
       $> fun p ->
          ( loc
          , fun fmt _ -> P.fmt_ppr_cmp_proof ps.context.cD ps.context.cG fmt p
          )
       end
  |> replace_locs

let add_new_mutual_rec_thmss target_file_name new_mutual_rec_thmss =
  let out_ch = open_out_gen [Open_append; Open_text] 0o600 target_file_name in
  let out_ppf = Format.formatter_of_out_channel out_ch in
  let printf_out fmt = Format.fprintf out_ppf fmt in
  new_mutual_rec_thmss
  |> List.iter
       begin fun thms ->
       printf_out "@.";
       printf_out "@[<v>";
       thms
       |> List.iteri
            begin fun i thm ->
            if i != 0
            then printf_out "and@,";
            Format.fprintf out_ppf "%a" Theorem.serialize thm
            end;
       printf_out ";@]@."
       end

module Prover = struct
  module Session = struct
    type t =
      { theorems : Theorem.t DynArray.t
      ; commands : Command.command DynArray.t
      ; name : Id.name
      ; mutual_group : CompS.mutual_group_id
      }

    let make name mutual_group thms =
      { theorems = thms
      ; commands = DynArray.make 32
      ; name
      ; mutual_group
      }

    (** Gets the list of mutual declarations corresponding to the
        currently loaded theorems in the active session.
     *)
    let get_mutual_decs (s : t) : Comp.total_dec list option =
      CompS.lookup_mutual_group s.mutual_group

    (** Unhides cids for all theorems in this session. *)
    let enter (s : t) : unit =
      DynArray.iter (fun t -> Theorem.set_hidden t false) s.theorems

    (** Hides cids for all theorems in this session. *)
    let suspend (s : t) : unit =
      DynArray.iter (fun t -> Theorem.set_hidden t true) s.theorems

    let remove_current_theorem s =
      DynArray.delete s.theorems 0

    let defer_theorem s =
      let t = DynArray.get s.theorems 0 in
      remove_current_theorem s;
      DynArray.add s.theorems t

    (** Gets the next theorem from the interpreter state.
        Returns `None` if there are no theorems left,
        i.e. all theorems in the mutual block have been proven.
     *)
    let next_theorem s : Theorem.t option =
      Misc.DynArray.head s.theorems

    (** Decides whether a given `cid` is in among the currently being
        proven theorems. *)
    let cid_is_in_current_theorem_set s c =
      List.exists (fun t -> Theorem.has_cid_of t c) (DynArray.to_list s.theorems)

    (** Infer invocation kind based on `exp_syn` and the current theorem
     *)
    let infer_invocation_kind s (i : Comp.exp_syn) : Comp.invoke_kind =
      match Comp.head_of_application i with
      | Comp.Const (_, c) when cid_is_in_current_theorem_set s c -> `ih
      | _ -> `lemma
  end

  module State = struct
    type t =
      { sessions : Session.t DynArray.t
      (* ^ The theorem sets currently being proven. *)

      ; automation_state : Automation.State.t
      ; prompt : InputPrompt.t
      ; ppf : Format.formatter
      ; stop : [ `stop | `go_on ]
      ; all_paths : string list
      }

    let recover_theorem ppf hooks (cid, gs) =
      let e = CompS.get cid in
      let initial_state =
        let s =
          Comp.make_proof_state [Id.render_name e.CompS.name]
            ( e.CompS.typ, Whnf.m_id )
        in
        let prf =
          match e.CompS.prog with
          | Some (Comp.ThmValue (_, Comp.Proof p, _, _)) -> p
          | _ -> B.Error.violation "recovered theorem not a proof"
        in
        dprintf begin fun p ->
          p.fmt "[recover_theorem] @[<v>proof =@,@[%a@]@]"
            P.(fmt_ppr_cmp_proof LF.Empty LF.Empty) prf
          end;
        s.Comp.solution := Some prf;
        s
      in
      Theorem.configure
        cid
        ppf
        hooks
        initial_state
        (Nonempty.to_list gs)

    let recover_session ppf hooks (mutual_group, thm_confs) =
      let name =
        Nonempty.head thm_confs |> fst |> CompS.name
      in
      let commands = DynArray.create () in
      let theorems =
        Nonempty.(
          map (recover_theorem ppf hooks) thm_confs
          |> to_list (* XXX to_list -> of_list is inefficient *)
        )
        |> DynArray.of_list
      in
      { Session.name; commands; theorems; mutual_group }

    let recover_sessions ppf hooks (gs : Comp.open_subgoal list) =
      (* idea:
         - first group subgoals by theorem
         - group theorems by mutual group
         - construct a session for each mutual group
       *)
      Nonempty.(
        group_by fst gs
        |> List.map (Pair.rmap (map snd))
        |> group_by F.(CompS.mutual_group ++ fst)
      )
      |> fun xs -> List.map (recover_session ppf hooks) xs

    let printf s x = Format.fprintf s.ppf x

    let defer_session s =
      let c = DynArray.get s.sessions 0 in
      DynArray.delete s.sessions 0;
      DynArray.add s.sessions c

    let next_session s = Misc.DynArray.head s.sessions

    (** Runs proof automation on a given subgoal. *)
    let run_automation auto_state (t : Theorem.t) (g : Comp.proof_state) =
      ignore (Automation.execute auto_state t g)

    (** Creates a prover state with sessions recovered from the given
        list of open subgoals.
        Use an empty list to generate a prover state with no sessions.
     *)
    let make
          stop
          (all_paths : string list)
          (ppf : Format.formatter)
          (prompt : InputPrompt.t)
          (gs : Comp.open_subgoal list)
        : t =
      let automation_state = Automation.State.make () in
      let hooks = [run_automation automation_state] in
      { sessions = DynArray.of_list (recover_sessions ppf hooks gs)
      ; automation_state
      ; prompt
      ; ppf
      ; stop
      ; all_paths
      }

    (**
     * TODO: Make this to preserve the order of sessions and theorems
     *)
    let reset_harpoon s =
      let forbid_leftover_vars path = function
        | None -> ()
        | Some vars ->
           let open Format in
           if !Debug.chatter <> 0 then
             fprintf std_formatter "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@."
               path
               B.Recsgn.fmt_ppr_leftover_vars vars;
           raise (B.Abstract.Error (B.Syntax.Loc.ghost, B.Abstract.LeftoverVars))
      in
      let load_file path =
        let sgn, leftover_vars =
          B.Parser.(B.Runparser.parse_file path (only sgn) |> extract)
          |> B.Recsgn.apply_global_pragmas
          |> B.Recsgn.recSgnDecls
        in
        B.Store.Modules.reset ();
        forbid_leftover_vars path leftover_vars
      in
      B.Store.clear ();
      B.Typeinfo.clear_all ();
      Holes.clear();
      List.iter load_file s.all_paths;
      let gs =
        B.Holes.get_harpoon_subgoals ()
        |> List.map snd
      in
      let hooks = [run_automation s.automation_state] in
      DynArray.clear s.sessions;
      DynArray.append s.sessions (DynArray.of_list (recover_sessions s.ppf hooks gs))

    (** Displays the given prompt `msg` and awaits a line of input from the user.
        The line is parsed using the given parser.
        In case of a parse error, the prompt is repeated.
        The user can abort the prompt by giving an empty string.
     *)
    let rec prompt_with s msg use_history (p : 'a B.Parser.t) : 'a option =
      match s.prompt msg use_history () with
      | None -> raise EndOfInput
      | Some "" -> None
      | Some line ->
         B.Runparser.parse_string "<prompt>" line (B.Parser.only p)
         |> snd
         |> B.Parser.handle
              begin fun err ->
              printf s "@[%a@]@."
                B.Parser.print_error err;
              prompt_with s msg use_history p
              end
              Maybe.pure

    (** Repeats the prompt even if the user gives an empty response. *)
    let rec prompt_forever_with s msg use_history p =
      match prompt_with s msg use_history p with
      | None -> prompt_forever_with s msg use_history p
      | Some x -> x

    (** Runs the theorem configuration prompt to construct a mutual
        group of theorems.
     *)
    let session_configuration_wizard' s : CompS.mutual_group_id * Theorem.t list =
      let rec do_prompts i : Theorem.Conf.t list =
        printf s "Configuring theorem #%d@." i;
        (* prompt for name, and allow using empty to signal we're done. *)
        match prompt_with s "  Name of theorem (empty name to finish): " None B.Parser.name with
        | None -> []
        | Some name ->
           let tau, k =
             (* XXX These calls are sketchy as hell.
                There must be a better place to put them -je
              *)
             B.Reconstruct.reset_fvarCnstr ();
             B.Store.FCVar.clear ();
             (* Now prompt for the statement, and disallow empty to signal we're done. *)
             prompt_forever_with s "  Statement of theorem: " None
               B.Parser.(cmp_typ $> Interactive.elaborate_typ LF.Empty)
           in
           dprintf begin fun p ->
             p.fmt "@[<v 2>[harpoon] [session_configuration] elaborated type\
                    @,@[%a@]\
                    @,with %d implicit parameters@]"
               P.(fmt_ppr_cmp_typ LF.Empty l0) tau
               k
             end;
           let order =
             let p =
               Misc.Function.flip B.Parser.map
                 B.Parser.(numeric_total_order |> span)
                 begin fun (loc, o) ->
                   let order = Interactive.elaborate_numeric_order tau o in
                   dprintf begin fun p ->
                     p.fmt "[session_configuration] @[<v>elaborated numeric order\
                            @,  @[%a@]\
                            @,considering %d implicit arguments.@]"
                       P.(fmt_ppr_cmp_numeric_order) order
                       k
                     end;
                   order
                     (* TODO we should check that the order is legit
                        here so that we can right away prompt the user
                        for a correct one; currently this check only
                        happens very late when the theorem set is
                        configured. *)
                 end
             in
             prompt_with s "  Induction order (empty for none): " None
               p
           in
           printf s "@]";
           let total_dec_kind =
             match order with
             | Some order -> `inductive order
             | None -> `not_recursive
           in
           let conf = Theorem.Conf.make name total_dec_kind tau k in
           conf :: do_prompts (i + 1)
      in

      let confs = do_prompts 1 in
      Theorem.configure_set s.ppf [run_automation s.automation_state] confs

    let add_session s c = DynArray.insert s.sessions 0 c
    let remove_current_session s = DynArray.delete s.sessions 0

    let session_configuration_wizard name s =
      let mutual_group, thms = session_configuration_wizard' s in
      (* c will be populated with theorems; if there are none it's
         because the session is over. *)
      match thms with
      | _ :: _ ->
         `ok (Session.make name mutual_group (DynArray.of_list thms))
      | [] -> `aborted
  end

    (*
  (** Removes the theorem with a given name from the list of theorems. *)
  let remove_theorem s name =
    let n = DynArray.length s.theorems in
    let rec loop = function
      | i when i >= n -> ()
      | i when Id.equals name (DynArray.get s.theorems i).Theorem.name ->
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

  let prompt s =
    (* The lambda character (or any other UTF-8 characters)
       does not work with linenoise.
       See https://github.com/ocaml-community/ocaml-linenoise/issues/13
       for detail.
     *)
    s.State.prompt "> " None ()
    |> Maybe.get' EndOfInput

  let process_command
        (s : State.t)
        (c : Session.t)
        (t : Theorem.t)
        (g : Comp.proof_state)
        (cmd : Command.command)
      : unit =
    let mfs =
      lazy
        begin
          let ds = Session.get_mutual_decs c |> Maybe.get_default [] in
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
      | Holes.CompInfo -> failwith "computational holes not supported"
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
           Logic.Convert.typToQuery cPsi cDh (typ, 0)
         in
         try
           Logic.Solver.solve cDh cPsi query
             begin fun (cPsi, tM) ->
             State.printf s "found solution: @[%a@]@,@?"
               (P.fmt_ppr_lf_normal cDh cPsi P.l0) tM;
             h.info.lfSolution <- Some (tM, LF.Shift 0);
             raise Logic.Frontend.Done
             end
         with
         | Logic.Frontend.Done ->
            State.printf s "logic programming finished@,@?";
            ()
    in

    let { cD; cG; cIH } = g.context in

    match cmd with
    (* Administrative commands: *)
    | Command.Theorem cmd ->
       begin match cmd with
       | `list ->
          let theorem_list = DynArray.to_list c.Session.theorems in
          let theorem_indexed_name_list =
            List.mapi (fun i thm -> (i, Theorem.get_name thm)) theorem_list
          in
          let fmt_ppr_indexed_theorem ppf (i, sName) =
            Format.fprintf ppf "%d. %a %s"
              i
              Id.print sName
              (if i = 0
               then "<<< current theorem"
               else ""
              )
          in
          let fmt_ppr_indexed_theorems =
            Format.pp_print_list ~pp_sep: Format.pp_print_cut fmt_ppr_indexed_theorem
          in
          (* It may be better to add the current session name to this message *)
          State.printf s "@[<v>Theorems in the current session:@,  @[<v>%a@]@]"
            fmt_ppr_indexed_theorems theorem_indexed_name_list
       | `defer -> Session.defer_theorem c
       | `show_ihs ->
          let f i =
            State.printf s "%d. @[%a@]@,"
              (i + 1)
              (P.fmt_ppr_cmp_ih g.context.cD g.context.cG)
          in
          State.printf s "@[<v>There are %d IHs:@,"
            (Context.length g.context.cIH);
          Context.to_list g.context.cIH |> List.iteri f;
          State.printf s "@]"
       | `dump_proof path ->
          dump_proof t path
       | `show_proof ->
          Theorem.show_proof t
       | `select name ->
          begin match
            Misc.DynArray.rfind_opt_idx
              c.Session.theorems
              (fun t -> Theorem.has_name_of t name)
          with
          | None ->
             State.printf s "No such theorem by name %a in the current session.@,"
               Id.print name
          | Some (i, t) ->
             DynArray.delete c.Session.theorems i;
             DynArray.insert c.Session.theorems 0 t
          end
       end
    | Command.Session cmd ->
       begin match cmd with
       | `list ->
          let session_list = DynArray.to_list s.State.sessions in
          let session_indexed_name_list =
            List.mapi (fun i s -> (i + 1, s.Session.name)) session_list
          in
          let fmt_ppr_indexed_session ppf (i, sName) =
            Format.fprintf ppf "%d. %a %s"
              i
              Id.print sName
              (if i = 0
               then "<<< current session"
               else ""
              )
          in
          let fmt_ppr_indexed_sessions =
            Format.pp_print_list ~pp_sep: Format.pp_print_cut fmt_ppr_indexed_session
          in
          State.printf s "@[<v>Sessions:@,  @[<v>%a@]@]"
            fmt_ppr_indexed_sessions session_indexed_name_list
       | `defer -> State.defer_session s
       | `create name ->
          begin match
            Misc.DynArray.rfind_opt_idx
              s.State.sessions
              (fun c -> Id.equals c.Session.name name)
          with
          | Some _ ->
             State.printf s "A session named %a already exists@,"
               Id.print name
          | None ->
             begin match State.session_configuration_wizard name s with
             | `ok c -> State.add_session s c
             | `aborted -> ()
             end
          end
       | `select name ->
          begin match
            Misc.DynArray.rfind_opt_idx
              s.State.sessions
              (fun c -> Id.equals c.Session.name name)
          with
          | None ->
             State.printf s "No such session by name %a.@,"
               Id.print name
          | Some (i, c) ->
             DynArray.delete s.State.sessions i;
             let c' = DynArray.get s.State.sessions 0 in
             Session.suspend c';
             Session.enter c;
             DynArray.insert s.State.sessions 0 c'
          end
       | `save ->
          let has_file_loc hole = hole |> fst |> Loc.is_ghost |> not in
          let existing_holes =
            Holes.get_harpoon_subgoals ()
            |> List.filter has_file_loc
          in
          (* If a theorem is in the state,
           * and it does not have any predefined holes in the loaded files,
           * that theorem is newly defined in this harpoon process.
           *)
          let is_new_theorem thm =
            existing_holes
            |> List.map (fun hole -> hole |> snd |> fst)
            |> List.find_opt (Theorem.has_cid_of thm)
            |> Option.is_none
          in
          let new_mutual_rec_thmss =
            DynArray.to_list s.State.sessions
            |> List.map
                 begin fun sess ->
                 sess.Session.theorems
                 |> DynArray.to_list
                 |> List.filter is_new_theorem
                 end
            |> List.filter (fun thms -> thms != [])
          in
          update_existing_holes existing_holes;
          add_new_mutual_rec_thmss
            (ExtList.List.last s.State.all_paths)
            new_mutual_rec_thmss;
          State.reset_harpoon s;
       end
    | Command.Subgoal cmd ->
       begin match cmd with
       | `list -> Theorem.show_subgoals t
       | `defer -> Theorem.defer_subgoal t
       end

    | Command.Rename (x_src, x_dst, level) ->
       Theorem.rename_variable x_src x_dst level t g

    | Command.ToggleAutomation (automation_kind, automation_change) ->
       Automation.toggle
         s.State.automation_state
         automation_kind
         automation_change

    | Command.Type i ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       State.printf s
         "- @[<hov 2>@[%a@] :@ @[%a@]@]"
         P.(fmt_ppr_cmp_exp_syn cD cG l0) i
         P.(fmt_ppr_cmp_typ cD l0) tau

    | Command.Info (k, name) ->
       begin match k with
       | `prog ->
          begin match
            try
              Some (CompS.index_of_name name |> CompS.get)
            with
            | Not_found -> None
          with
          | None ->
             State.printf s
               "- No such theorem by name %a" Id.print name
          | Some e ->
             State.printf s
               "- @[%a@]"
               P.fmt_ppr_cmp_comp_prog_info e
          end
       end

    (* Real tactics: *)
    | Command.Unbox (i, name) ->
       let (hs, m, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.unbox m tau name t g

    | Command.Intros names ->
       Tactic.intros names t g

    | Command.Split (split_kind, i) ->
       let (hs, m, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       Tactic.split split_kind m tau (Lazy.force mfs) t g
    | Command.MSplit (loc, name) ->
       let i, tau = Elab.mvar cD loc name in
       Tactic.split `split i tau (Lazy.force mfs) t g
    | Command.By (i, name, b) ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       dprintf
         begin fun p ->
         p.fmt "@[<v>[harpoon-By] elaborated invocation:@,%a@ : %a@]"
           (P.fmt_ppr_cmp_exp_syn cD cG P.l0) i
           (P.fmt_ppr_cmp_typ cD P.l0) tau
         end;
       List.iter solve_hole hs;
       Tactic.invoke b i tau name t g

    | Command.Suffices (i, tau_list) ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       begin match Session.infer_invocation_kind c i with
       | `ih ->
          State.printf s "inductive use of `suffices by ...` is not currently supported"
       | `lemma ->
          begin match hs with
          | _ :: _ ->
             Theorem.printf t "holes are not supported for `suffices by _ ...`"
          | [] ->
             let tau_list = List.map (Elab.typ cD) tau_list in
             Tactic.suffices i tau_list tau t g
          end
       end

    | Command.Solve e ->
       let (hs, e) = Elab.exp cIH cD cG (Lazy.force mfs) e g.goal in
       dprnt "[harpoon] [solve] elaboration finished";
       (* State.printf s "Found %d hole(s) in solution@." (List.length hs); *)
       List.iter solve_hole hs;
       dprnt "[harpoon] [solve] double-check!";
       Check.Comp.check cD cG (Lazy.force mfs) ~cIH: cIH e g.goal;
       dprnt "[harpoon] [solve] double-check DONE";
       (Comp.solve e |> Tactic.solve) t g

  let record_command c cmd = DynArray.add c.Session.commands cmd
end

(** A computed value of type 'a or a function to print an error. *)
type 'a error = (Format.formatter -> unit -> unit, 'a) Either.t

(** Parses the given string to a Syntax.Ext.Harpoon.command or an
    error-printing function.
 *)
let parse_input (input : string) : Command.command list error =
  let open B in
  Runparser.parse_string "<prompt>" input
    Parser.(only interactive_harpoon_command_sequence)
  |> snd |> Parser.to_either
  |> Either.lmap (fun e ppf () -> Parser.print_error ppf e)

(** Runs the given function, trapping exceptions in Either.t
    and converting the exception to a function that prints the
    error with a given formatter.
 *)
let run_safe (f : unit -> 'a) : 'a error =
  try
    Either.Right (f ())
  with
  | e ->
     let s = Printexc.to_string e in
     let bt = Printexc.get_backtrace () in
     Either.Left
       begin fun ppf () ->
       Format.fprintf ppf "@[<v>Internal error. (State may be undefined.)@,%s@,%s@]"
         s bt
       end

(** Gets the next state triple from the prover.
 *)
let with_next_triple (s : Prover.State.t) =
  match Prover.State.next_session s with
  | None -> Either.Left `no_session
  | Some c ->
     match Prover.Session.next_theorem c with
     | None -> Either.Left (`no_theorem c)
     | Some t ->
        match Theorem.next_subgoal t with
        | None -> Either.Left (`no_subgoal (c, t))
        | Some g -> Either.Right (c, t, g)

(** Parses the user input string and executes it in the given state
    triple.
    The input command sequence must be fully executable in the
    current theorem.
    Returns:
    - `ok: all commands were executed in the current theorem
    - `stopped_short: some commands were not executed because the
      current theorem is over.
    - `error: an error occurred. Commands beyond the failed one were
      not executed.
 *)
let process_input s (c, t, g) input =
  let printf x = Prover.State.printf s x in
  let e =
    let open Either in
    parse_input input
    $ fun cmds ->
      (* Idea:
         - count the commands to run
         - count the commands we were able to process
       *)
      let n = List.length cmds in
      run_safe
        begin fun () ->
        let (k, _) =
          List.fold_left
            begin fun (k, g) cmd ->
            match g with
            | None -> (k, g)
            | Some g ->
               Prover.process_command s c t g cmd;
               Prover.record_command c cmd;
               (k + 1, Theorem.next_subgoal t)
            end
            (0, Some g)
            cmds
        in
        n = k
        end
  in
  Either.eliminate
    begin fun f ->
    printf "%a" f ();
    if Prover.(s.State.stop) = `stop then
      exit 1;
    `error
    end
    (function
     | true -> `ok
     | false -> `stopped_short)
    e

let rec loop (s : Prover.State.t) : unit =
  let printf x = Prover.State.printf s x in
  match with_next_triple s with
  | Either.Left `no_session ->
     let name = Id.(mk_name (SomeString "default")) in
     begin match Prover.State.session_configuration_wizard name s with
     | `ok c ->
        Prover.State.add_session s c;
        loop s
     | `aborted ->
        printf "@,Harpoon terminated.@,"
     end
  | Either.Left (`no_theorem _) ->
     printf "@,Proof complete! (No theorems left.)@,";
     (* TODO: record proof to file by retrieving the proofs of each
        theorem in the store.
      *)
     (* printf "Record proof to file %s? ";
        s.prompt "[Y/n] " None ()
      *)
     Prover.State.remove_current_session s;
     loop s
  | Either.Left (`no_subgoal (c, t)) ->
     (* TODO: record the proof into the Store *)
     printf "@[<v>Subproof complete! (No subgoals left.)@,@]";
     Theorem.show_proof t;
     Prover.Session.remove_current_theorem c;
     loop s
  | Either.Right (c, t, g) ->
    (* Show the proof state and the prompt *)
    printf "@,@[<v>@,%a@,@]@?"
      P.fmt_ppr_cmp_proof_state g;
    (*
      printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
      P.fmt_ppr_cmp_proof_state g
      (Context.length Comp.(g.context.cIH));
     *)

    (* Parse the input and run the command *)
    let input = Prover.prompt s in
    match process_input s (c, t, g) input with
    | `ok | `error -> loop s
    | `stopped_short ->
       printf "@,Warning: theorem proven before all commands were processed.@,";
       loop s

type interaction_mode = [ `stop | `go_on ]

let start_toplevel
      (stop : interaction_mode)
      (all_paths : string list)
      (gs : Comp.open_subgoal list)
      (input_prompt : InputPrompt.t)
      (ppf : Format.formatter) (* The formatter used to display messages *)
    : unit =
  let open Prover in
  let s = State.make stop all_paths ppf input_prompt gs in
  (* If no sessions were created by loading the subgoal list
     then (it must have been empty so) we need to create the default
     session and configure it. *)
  if DynArray.empty State.(s.sessions) then
    let name = Id.(mk_name (SomeString "default")) in
    match State.session_configuration_wizard name s with
    | `ok c ->
       State.add_session s c;
       loop s
    | `aborted -> ()
  else
    loop s
