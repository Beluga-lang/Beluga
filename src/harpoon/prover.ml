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
      let e = Interactive.elaborate_exp cD cG t ttau in
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
           P.(fmt_ppr_cmp_meta_typ cD l0) cT
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

module Prover = struct
  module Session = struct
    type t =
      { theorems : Theorem.t DynArray.t
      ; commands : Command.command DynArray.t
      ; name : Id.name
      }

    let make name =
      { theorems = DynArray.make 16
      ; commands = DynArray.make 32
      ; name
      }

    (** Gets the list of mutual declarations corresponding to the
        currently loaded theorems in the active session.
     *)
    let get_mutual_decs (s : t) : Total.dec list =
      List.map Theorem.total_dec (DynArray.to_list s.theorems)

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
      List.exists (fun t -> t.Theorem.cid = c) (DynArray.to_list s.theorems)

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

      ; automation_state : Automation.automation_state
      ; prompt : InputPrompt.t
      ; ppf : Format.formatter
      ; stop : [ `stop | `go_on ]
      }

    (** Creates a prover state no session. *)
    let make
          stop
          (ppf : Format.formatter)
          (prompt : InputPrompt.t)
        : t =
      { sessions = DynArray.make 16
      ; automation_state = Automation.make_automation_state ()
      ; prompt
      ; ppf
      ; stop
      }

    let printf s x = Format.fprintf s.ppf x

    let defer_session s =
      let c = DynArray.get s.sessions 0 in
      DynArray.delete s.sessions 0;
      DynArray.add s.sessions c

    let next_session s = Misc.DynArray.head s.sessions

    (** Runs proof automation on a given subgoal. *)
    let run_automation s (t : Theorem.t) (g : Comp.proof_state) =
      ignore (Automation.exec_automation s.automation_state t g)

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
              printf s "@[<v>Parse error.@,@[%a@]@]@."
                B.Parser.print_error err;
              prompt_with s msg use_history p
              end
              Maybe.pure

    (** Repeats the prompt even if the user gives an empty response. *)
    let rec prompt_forever_with s msg use_history p =
      match prompt_with s msg use_history p with
      | None -> prompt_forever_with s msg use_history p
      | Some x -> x

    (** Runs the theorem configuration prompt to populate the given
        session.
     *)
    let session_configuration_wizard s c : unit =
      assert (DynArray.length c.Session.theorems = 0);
      let rec do_prompts i : Theorem.Conf.t list =
        printf s "Configuring theorem #%d@." i;
        (* prompt for name, and allow using empty to signal we're done. *)
        match prompt_with s "  Name of theorem (empty name to finish): " None B.Parser.name with
        | None -> []
        | Some name ->
           let stmt, k =
             (* XXX These calls are sketchy as hell.
                There must be a better place to put them -je
              *)
             B.Reconstruct.reset_fvarCnstr ();
             B.Store.FCVar.clear ();
             (* Now prompt for the statement, and disallow empty to signal we're done. *)
             prompt_forever_with s "  Statement of theorem: " None
               B.Parser.cmp_typ
             |> Interactive.elaborate_typ LF.Empty
           in
           let order =
             prompt_with s "  Induction order (empty for none): " None
               B.Parser.numeric_total_order
             |> Maybe.map (Interactive.elaborate_numeric_order k)
           in
           printf s "@]";
           { Theorem.Conf.name; order; stmt } :: do_prompts (i + 1)
      in

      let confs = do_prompts 1 in
      let thms = Theorem.configure_set s.ppf [run_automation s] confs in
      Misc.DynArray.append_list c.Session.theorems thms

    let add_session s c = DynArray.insert s.sessions 0 c
    let remove_current_session s = DynArray.delete s.sessions 0
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

  let process_command
        (s : State.t)
        (c : Session.t)
        (t : Theorem.t)
        (g : Comp.proof_state)
        (cmd : Command.command)
      : unit =
    let mfs = lazy (Session.get_mutual_decs c) in

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
       | `list -> failwith "list theorems in session"
       | `defer -> Session.defer_theorem c
       | `show_ihs ->
          let f i =
            State.printf s "%d. %a@,"
              (i + 1)
              (P.fmt_ppr_cmp_ctyp_decl g.context.cD P.l0)
          in
          State.printf s "There are %d IHs:@,"
            (Context.length g.context.cIH);
          Context.to_list g.context.cIH |> List.iteri f
       | `show_proof ->
          Theorem.show_proof t
       | `select name ->
          begin match
            Misc.DynArray.findi_opt
              c.Session.theorems
              (fun t -> Id.equals t.Theorem.name name)
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
       | `list -> failwith "list sessions in state"
       | `defer -> State.defer_session s
       | `create name ->
          begin match
            Misc.DynArray.findi_opt
              s.State.sessions
              (fun c -> Id.equals c.Session.name name)
          with
          | Some _ ->
             State.printf s "A session named %a already exists@,"
               Id.print name
          | None ->
             let c = Session.make name in
             State.session_configuration_wizard s c;
             State.add_session s c
          end
       | `select name ->
          begin match
            Misc.DynArray.findi_opt
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
       end
    | Command.Subgoal cmd ->
       begin match cmd with
       | `list -> Theorem.show_subgoals t
       | `defer -> Theorem.defer_subgoal t
       end

    | Command.Rename (x_src, x_dst, level) ->
       Theorem.rename_variable x_src x_dst level t g

    | Command.ToggleAutomation (automation_kind, automation_change) ->
       Automation.toggle_automation
         s.State.automation_state
         automation_kind
         automation_change

    | Command.Type i ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       B.Printer.with_implicits false
         begin fun () ->
         State.printf s
           "- @[<hov 2>@[%a@] :@ @[%a@]@]"
           P.(fmt_ppr_cmp_exp_syn cD cG l0) i
           P.(fmt_ppr_cmp_typ cD l0) tau
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
       let k = Session.infer_invocation_kind c i in
       Tactic.invoke k b i tau name t g

    | Command.Suffices (i, tau_list) ->
       let (hs, i, tau) = Elab.exp' cIH cD cG (Lazy.force mfs) i in
       begin match Session.infer_invocation_kind c i with
       | `ih ->
          State.printf s "inductive use of `suffices by _ ...` is not currently supported"
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
       Check.Comp.check cD cG (Lazy.force mfs) e g.goal;
       (Comp.solve e |> Tactic.solve) t g

  let record_command c cmd = DynArray.add c.Session.commands cmd
end

(** A computed value of type 'a or a function to print an error. *)
type 'a error = (Format.formatter -> unit -> unit, 'a) Either.t

(** Parses the given string to a Syntax.Ext.Harpoon.command or an
    error-printing function.
 *)
let parse_input (input : string) : Command.command error =
  let open B in
  Runparser.parse_string "<prompt>" input Parser.(only interactive_harpoon_command)
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

let rec loop (s : Prover.State.t) : unit =
  let printf x = Prover.State.printf s x in
  (* Get the next subgoal *)
  match Prover.State.next_session s with
  | None ->
     let c = Prover.Session.make Id.(mk_name (SomeString "default")) in
     Prover.State.session_configuration_wizard s c;
     (* c will be populated with theorems; if there are none it's
        because the session is over. *)
     begin match DynArray.length Prover.(c.Session.theorems) > 0 with
     | true ->
        Prover.State.add_session s c;
        loop s
     | false -> printf "@,Harpoon terminated.@,"
     end
  | Some c ->
     match Prover.Session.next_theorem c with
     | None ->
        printf "@,Proof complete! (No theorems left.)@,";
        (* printf "Record proof to file %s? ";
        s.prompt "[Y/n] " None ()
         *)
        Prover.State.remove_current_session s;
        loop s;
     | Some t ->
        match Theorem.next_subgoal t with
        | None ->
           printf "@,Subproof complete! (No subgoals left.)@,";
           Theorem.show_proof t;
           Prover.Session.remove_current_theorem c;
           loop s
        | Some g ->
           (* Show the proof state and the prompt *)
           printf "@,@[<v>@,%a@,@]@?"
             P.fmt_ppr_cmp_proof_state g;
           (*
             printf "@,@[<v>@,%a@,There are %d IHs.@,@]@?"
             P.fmt_ppr_cmp_proof_state g
             (Context.length Comp.(g.context.cIH));
            *)

           (* Parse the input and run the command *)
           let input =
             let open Prover in
             (* The lambda character (or any other UTF-8 characters)
                does not work with linenoise.
                See https://github.com/ocaml-community/ocaml-linenoise/issues/13
                for detail.
              *)
             s.State.prompt "> " None ()
             |> Maybe.get' EndOfInput
           in
           let e =
             let open Either in
             parse_input input
             $ fun cmd ->
               run_safe
                 begin fun () ->
                 Prover.process_command s c t g cmd;
                 Prover.record_command c cmd
                 end
           in
           Either.eliminate
             begin fun f ->
             printf "%a" f ();
             if Prover.(s.State.stop) = `stop then
               exit 1
             end
             (Misc.const ())
             e;
           loop s

let start_toplevel
      stop
      (prompt : InputPrompt.t)
      (ppf : Format.formatter) (* The formatter used to display messages *)
    : unit =
  let open Prover in
  let s = State.make stop ppf prompt in
  let c = Session.make Id.(mk_name (SomeString "default")) in
  Prover.State.session_configuration_wizard s c;
  State.add_session s c;
  loop s
