open Support
open Beluga_syntax.Common
open Beluga_syntax.Synint

module F = Fun

module P = Beluga.Prettyint.DefaultPrinter

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [14]))
open Debug.Fmt

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
  let e = Store.Cid.Comp.get cid in
  let tau = e.Store.Cid.Comp.Entry.typ in
  let decl = Store.Cid.Comp.get_total_decl cid in
  let initial_state =
    let s =
      make_proof_state SubgoalPath.start
        ( Total.annotate Beluga_syntax.Location.ghost decl.Comp.order tau
        , Whnf.m_id )
    in
    let prf =
      match e.Store.Cid.Comp.Entry.prog with
      | Some (ThmValue (_, Proof p, _, _)) -> p
      | _ -> Beluga_syntax.Error.raise_violation "recovered theorem not a proof"
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
    (List1.to_list gs)

let recover_session ppf hooks (mutual_group, thm_confs) =
  let theorems =
    let f = recover_theorem ppf hooks in
    (* XXX to_list -> of_list later is inefficient
           It would be best to add a function to obtain a Seq.t from
           an List1.t, lazily map the sequence, and the force the
           sequence with DynArray.of_seq
     *)
    List1.map f thm_confs |> List1.to_list
  in
  dprintf begin fun p ->
    p.fmt "[recover_session] @[<v>recovered a session with the following theorems:\
           @,  @[<hv>%a@]@]"
      (Format.pp_print_list ~pp_sep: Format.comma
         (fun ppf t -> Format.fprintf ppf "%a" Name.pp (Theorem.get_name t)))
      theorems
    end;
  Session.make mutual_group theorems

(** Constructs a list of sessions from a list of open subgoals.
    Subgoals are grouped into theorems according to their
    associated cid, and theorems are grouped into sessions
    according to their mutual group.
 *)
let recover_sessions ppf hooks (gs : Comp.open_subgoal list) =
  (* idea:
     - first group subgoals by theorem
     - group theorems by mutual group
     - construct a session for each mutual group
   *)
  List1.group_by Pair.fst gs
  |> List.map (Pair.map_right (List1.map Pair.snd))
  |> List1.group_by F.(Pair.fst >> Store.Cid.Comp.mutual_group)
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

let next_session s = DynArray.head s.sessions

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
  let sessions =
    recover_sessions (IO.formatter io) hooks gs
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
    it.
 *)
let select_session s i c =
  (* remove the target session (i.e. c) from the list *)
  DynArray.delete s.sessions i;
  (* make the target session the active session by moving it to position 0 *)
  DynArray.insert s.sessions 0 c

(** Adds a session to the prover and selects it. *)
let add_session s c =
  let k = DynArray.length s.sessions in
  DynArray.add s.sessions c;
  (* newly added session is at index k *)
  select_session s k c

(** Finds a session containing a theorem with the given name and
    selects that session and that theorem.
    Returns false when no theorem by such name could be found.
 *)
let select_theorem s name =
  match
    DynArray.rfind_opt_idx
      s.sessions
      F.(Option.is_some ++ flip Session.lookup_theorem name)
  with
  | None -> false
  | Some (i, c) ->
     select_session s i c;
     (* select the desired theorem within the session;
            this should be guaranteed to succeed due to the
            lookup_theorem having succeeded in this case *)
     if Bool.not (Session.select_theorem c name) then
      Beluga_syntax.Error.raise_violation
         "[select_theorem] selected session does not contain the theorem";
     true

(** Gets the next state triple from the prover. *)
let next_triple (s : t) =
  match next_session s with
  | None -> Either.left `no_session
  | Some c ->
     match Session.next_theorem c with
     | None -> Either.left (`no_theorem c)
     | Some t ->
        match Theorem.next_subgoal t with
        | None -> Either.left (`no_subgoal (c, t))
        | Some g -> Either.right (c, t, g)

(** Drops all state and reloads from the signature.
    Typically, this is called after serialization reflects the
    state into the signature.
    Note that the current state triple is not preserved by this
    call, and that after it, the prover may be focussing on a
    different subgoal, possibly in a different session/theorem.
    To preserve focus, combine this with `keeping_focus`. *)
let reset s : unit =
  let (_all_paths, _sgn') = Load.load_fresh s.sig_path in
  let gs = Holes.get_harpoon_subgoals () |> List.map Pair.snd in
  let hooks = [run_automation s.automation_state] in
  let cs =
    recover_sessions (IO.formatter s.io) hooks gs
  in
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
  if Bool.not (select_theorem s curr_thm_name) then
    Beluga_syntax.Error.raise_violation
      "[reset] reloaded signature does not contain the theorem \
       we were working on";
  let t =
    match next_triple s with
    | Either.Right (_, t, _) -> t
    | _ ->
      Beluga_syntax.Error.raise_violation
         "[reset] next_triple didn't give a triple."
  in
  match
    Theorem.select_subgoal_satisfying t
      begin fun g ->
      Whnf.conv_subgoal_path_builder g.Comp.label curr_sg_label
      end
  with
  | None ->
      Beluga_syntax.Error.raise_violation
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
    |> List.filter List.nonempty
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
  let open Option in
  Session.configuration_wizard s.io
    [run_automation s.automation_state]
  $> add_session s
  |> is_some

let on_session_completed s c =
  match save_mode s with
  | `save_back -> save s; reset s
  | `no_save_back ->
     remove_current_session s

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
    (print_list print_indexed_session) (List.index session_list)
