open Support
open Beluga.Syntax.Int

module F = Misc.Function
module DynArray = Misc.DynArray

module CompS = Beluga.Store.Cid.Comp
module P = Beluga.Pretty.Int.DefaultPrinter

let dprintf, _, _ = Beluga.Debug.(makeFunctions' (toFlags [14]))
open Beluga.Debug.Fmt

type triple = Session.t * Theorem.t * Comp.proof_state

type triple_error =
  [ `no_session
  | `no_theorem of Session.t
  | `no_subgoal of Session.t * Theorem.t
  ]

type triple_status = (triple_error, triple) Either.t

type t =
  { sessions : Session.t DynArray.t
  (* ^ The theorem sets currently being proven. *)

  ; automation_state : Automation.State.t
  ; io : IO.t
  ; save_back : Options.save_mode
  ; stop : Options.interaction_mode
  ; sig_path : string (* path to the signature that was loaded *)
  ; all_paths : string list (* paths to the resolved loaded files *)
  }

(* open beluga here because we need to refer to Harpoon's Options
   module earlier. *)
open Beluga

(** Constructs a Theorem.t for the given cid with the given
    subgoals. *)
let recover_theorem ppf hooks (cid, gs) =
  let open Comp in
  let e = CompS.get cid in
  let initial_state =
    let s =
      make_proof_state SubgoalPath.start
        ( e.CompS.Entry.typ, Whnf.m_id )
    in
    let prf =
      match e.CompS.Entry.prog with
      | Some (ThmValue (_, Proof p, _, _)) -> p
      | _ -> Error.violation "recovered theorem not a proof"
    in
    dprintf begin fun p ->
      p.fmt "[recover_theorem] @[<v>proof =@,@[%a@]@]"
        P.(fmt_ppr_cmp_proof LF.Empty LF.Empty) prf
      end;
    s.solution := Some prf;
    s
  in
  Theorem.configure
    cid
    ppf
    hooks
    initial_state
    (Nonempty.to_list gs)

let recover_session ppf hooks (mutual_group, thm_confs) =
  let theorems =
    let open Nonempty in
    let f =
      (* after recovering the theorem, set it hidden.
             later, we enter the session, which will bring it into
             scope. *)
      F.((fun t -> Theorem.set_hidden t true; t) ++ recover_theorem ppf hooks)
    in
    (* XXX to_list -> of_list later is inefficient
           It would be best to add a function to obtain a Seq.t from
           an Nonempty.t, lazily map the sequence, and the force the
           sequence with DynArray.of_seq
     *)
    map f thm_confs |> to_list
  in
  dprintf begin fun p ->
    p.fmt "[recover_session] @[<v>recovered a session with the following theorems:\
           @,  @[<hv>%a@]@]"
      (Format.pp_print_list ~pp_sep: Fmt.comma
         (fun ppf t -> Format.fprintf ppf "%a" Id.print (Theorem.get_name t)))
      theorems
    end;
  Session.make mutual_group theorems

(** Constructs a list of sessions from a list of open subgoals.
        Subgoals are grouped into theorems according to their
        associated cid, and theorems are grouped into sessions
        according to their mutual group.

        WARNING: all recovered theorems are hidden (out of scope).
        It is necessary to enter the session that ends up selecteed to
        bring its theorems into scope.
 *)
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
  |> List.map (recover_session ppf hooks)

(** Drops all sessions from the prover, replacing with the given
        list.
 *)
let replace_sessions s ss =
  DynArray.(clear s.sessions; append_list s.sessions ss)

let printf s x = IO.printf s.io x

let session_list s = DynArray.to_list s.sessions

(** Moves the current session to the back of the session list,
        making (what was) the second session the active session. *)
let defer_session s =
  let c = DynArray.get s.sessions 0 in
  DynArray.delete s.sessions 0;
  DynArray.add s.sessions c

let next_session s = Misc.DynArray.head s.sessions

let remove_current_session s =
  DynArray.delete s.sessions 0

(** Runs proof automation on a given subgoal. *)
let run_automation auto_state (t : Theorem.t) (g : Comp.proof_state) =
  ignore (Automation.execute auto_state t g)

(** Creates a prover state with sessions recovered from the given
        list of open subgoals.
        Use an empty list to generate a prover state with no sessions.
 *)
let make
      save_back
      stop
      (sig_path : string)
      (all_paths : string list)
      (io : IO.t)
      (gs : Comp.open_subgoal list)
    : t =
  let automation_state = Automation.State.make () in
  let hooks = [run_automation automation_state] in
  let sessions = recover_sessions (IO.formatter io) hooks gs in
  let _ =
    (* since all recovered sessions are suspended, we must
           explicitly enter the first one *)
    let open Maybe in
    Misc.List.hd_opt sessions
    $> Session.enter
  in
  { sessions = DynArray.of_list sessions
  ; automation_state
  ; io
  ; save_back
  ; stop
  ; sig_path
  ; all_paths
  }

(** Given that session `c` is at index `i` in the sessions list,
    `select_session s i c` moves it to the front, thus activating
    it.Takes care of suspending the active session and entering
    `c`. *)
let select_session s i c =
  (* get the active session *)
  let c' = DynArray.get s.sessions 0 in
  (* remove the target session (i.e. c) from the list *)
  DynArray.delete s.sessions i;
  (* suspend the current session and enter the target session *)
  Session.suspend c';
  Session.enter c;
  (* make the target session the active session by moving it to position 0 *)
  DynArray.insert s.sessions 0 c

(** Adds a session to the prover and selects it.
    If another session was selected before, it is suspended, and
    the new session is entered.
 *)
let add_session s c =
  let k = DynArray.length s.sessions in
  DynArray.add s.sessions c;
  (* newly added session is at index k *)
  select_session s k c
(*
    let remove_current_session s = DynArray.delete s.sessions 0
 *)

(** Finds a session containing a theorem with the given name and
    selects that session and that theorem.
    Returns false when no theorem by such name could be found.
 *)
let select_theorem s name =
  match
    Misc.DynArray.rfind_opt_idx
      s.sessions
      F.(Maybe.is_some ++ flip Session.lookup_theorem name)
  with
  | None -> false
  | Some (i, c) ->
     select_session s i c;
     (* select the desired theorem within the session;
            this should be guaranteed to succeed due to the
            lookup_theorem having succeeded in this case *)
     if not (Session.select_theorem c name) then
       Error.violation
         "[select_theorem] selected session does not contain the theorem";
     true

(** Gets the next state triple from the prover. *)
let next_triple (s : t) =
  match next_session s with
  | None -> Either.Left `no_session
  | Some c ->
     match Session.next_theorem c with
     | None -> Either.Left (`no_theorem c)
     | Some t ->
        match Theorem.next_subgoal t with
        | None -> Either.Left (`no_subgoal (c, t))
        | Some g -> Either.Right (c, t, g)

(** Drops all state and reloads from the signature.
    Typically, this is called after serialization reflects the
    state into the signature.
    Note that the current state triple is not preserved by this
    call, and that after it, the prover may be focussing on a
    different subgoal, possibly in a different session/theorem.
    To preserve focus, combine this with `keeping_focus`. *)
let reset s : unit =
  let _ = Load.load (IO.formatter s.io) s.sig_path in
  let gs = Holes.get_harpoon_subgoals () |> List.map snd in
  let hooks = [run_automation s.automation_state] in
  let cs = recover_sessions (IO.formatter s.io) hooks gs in
  dprintf begin fun p ->
    p.fmt "[reset] recovered %d sessions from %d subgoals"
      (List.length cs)
      (List.length gs)
    end;
  replace_sessions s cs

(** Takes note of the currently selected session, theorem, and
    subgoal, runs the given function, and then reselects the theorem
    and subgoal.  This is used by the serialize function to make sure
    that after serializing the Harpoon state, we're back in the same
    subgoal we were in before. *)
let keeping_focus s (c, t, g) f =
  let curr_thm_name = Theorem.get_name t in
  let curr_sg_label = g.Comp.label in
  f ();
  if not (select_theorem s curr_thm_name) then
    Error.violation
      "[reset] reloaded signature does not contain the theorem \
       we were working on";
  let t =
    match next_triple s with
    | Either.Right (_, t, _) -> t
    | _ ->
       Error.violation
         "[reset] next_triple didn't give a triple."
  in
  match
    Theorem.select_subgoal_satisfying t
      begin fun g ->
      Whnf.conv_subgoal_path_builder g.Comp.label curr_sg_label
      end
  with
  | None ->
     Error.violation
       "[reset] select_subgoal_satisfying returned None"
  | Some _ -> ()

(** Reflects the current prover state back into the loaded signature
    file.
    You should reset the prover state after doing this by calling
    `reset`.
 *)
let save s =
  let existing_holes =
    Holes.get_harpoon_subgoals ()
    |> List.map (fun (loc, (_, g)) -> (loc, g))
  in
  let new_mutual_rec_thmss =
    DynArray.to_list s.sessions
    |> List.filter
         begin fun sess ->
         match Session.get_session_kind sess with
         | `introduced -> true
         | `loaded -> false
         end
    |> List.map Session.full_theorem_list
    |> List.filter Misc.List.nonempty
  in
  Serialization.update_existing_holes existing_holes;
  Serialization.append_sessions
    (ExtList.List.last s.all_paths)
    new_mutual_rec_thmss

let automation_state s = s.automation_state

let interaction_mode s = s.stop

let save_mode s = s.save_back

let completeness s = match DynArray.length s.sessions with
  | 0 -> `complete
  | _ -> `incomplete

let parsed_prompt s ?(source = IO.default_prompt_source) msg use_history p =
  IO.parsed_prompt s.io ~source: source msg use_history p

let session_configuration_wizard s =
  let open Maybe in
  Session.configuration_wizard s.io
    [run_automation s.automation_state]
  $> add_session s
  |> is_some

let on_session_completed s =
  match save_mode s with
  | `save_back -> save s; reset s
  | `no_save_back -> remove_current_session s

let serialize s ctg = keeping_focus s ctg (fun _ -> save s; reset s)

let fmt_ppr_session_list ppf s =
  let session_list = session_list s in
  let print_list f ppf x =
    Format.(pp_print_list ~pp_sep: pp_print_cut f ppf x)
  in
  let print_indexed_session ppf (i, c) =
    Format.fprintf ppf "%d. @[<v>%a@]"
      (i + 1)
      Session.fmt_ppr_theorem_list c
  in
  printf s "@[<v>%a@]"
    (print_list print_indexed_session) (Misc.List.index session_list)
