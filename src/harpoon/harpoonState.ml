open Support
open Beluga_syntax.Syncom
open Beluga_syntax.Synint

module F = Fun

module P = Beluga.Prettyint.DefaultPrinter

module Disambiguation_state = Beluga_parser.Disambiguation_state.Disambiguation_state
module Indexing_state = Beluga.Index_state.Indexing_state

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [14]))
open Debug.Fmt

type substate =
  { session: Session.t
  ; theorem: Theorem.t
  ; proof_state: Comp.proof_state
  }

exception No_session

exception No_theorem of Session.t

exception No_subgoal of { session: Session.t; theorem: Theorem.t }

type t =
  { sessions : Session.t DynArray.t
  (* ^ The theorem sets currently being proven. *)

  ; disambiguation_state : Disambiguation_state.state
  ; indexing_state : Indexing_state.state
  ; automation_state : Automation.State.t
  ; io : IO.t
  ; save_back : Options.save_mode
  ; stop : Options.interaction_mode
  ; sig_path : string (* path to the signature that was loaded *)
  ; all_paths : string list (* paths to the resolved loaded files *)
  }

let with_io s f = f s.io

(* open beluga here because we need to refer to Harpoon's [Options]
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
      | Option.Some (ThmValue (_, Proof p, _, _)) -> p
      | _ -> Error.raise_violation "recovered theorem not a proof"
    in
    dprintf begin fun p ->
      p.fmt "[%s] @[<v>proof =@,@[%a@]@]"
        __FUNCTION__
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

let recover_session disambiguation_states indexing_states ppf hooks (mutual_group, thm_confs) =
  let theorems =
    List1.map
      (fun (cid, proof_state) -> recover_theorem ppf hooks (cid, proof_state))
      thm_confs
  in
  let first_theorem_conf = List1.head theorems in
  let first_theorem_cid = Theorem.get_cid first_theorem_conf in
  let disambiguation_state = Id.Prog.Hashtbl.find disambiguation_states first_theorem_cid in
  let indexing_state = Id.Prog.Hashtbl.find indexing_states first_theorem_cid in
  dprintf begin fun p ->
    p.fmt "[%s] @[<v>recovered a session with the following theorems:\
           @,  @[<hv>%a@]@]"
      __FUNCTION__
      (List1.pp ~pp_sep:Format.comma
         (fun ppf t -> Format.fprintf ppf "%a" Name.pp (Theorem.get_name t)))
      theorems
    end;
  Session.make disambiguation_state indexing_state mutual_group (List1.to_list theorems)

(** Constructs a list of sessions from a list of open subgoals.
    Subgoals are grouped into theorems according to their
    associated cid, and theorems are grouped into sessions
    according to their mutual group.
 *)
let recover_sessions disambiguation_states indexing_states ppf hooks (gs : Comp.open_subgoal list) =
  (* idea:
     - first group subgoals by theorem
     - group theorems by mutual group
     - construct a session for each mutual group
   *)
  List1.group_by (fun (_location, theorem_cid, _state) -> theorem_cid) gs
  |> List.map
       (fun (theorem_cid, subgoals) ->
          let subgoals' =
            List1.map
              (fun (_location, _cid, proof_state) -> proof_state)
              subgoals
          in
          (theorem_cid, subgoals'))
  |> List1.group_by (fun (theorem_cid, _) ->
        Store.Cid.Comp.mutual_group theorem_cid)
  |> List.map (recover_session disambiguation_states indexing_states ppf hooks)

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
      (disambiguation_states, disambiguation_state)
      (indexing_states, indexing_state)
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
    recover_sessions disambiguation_states indexing_states (IO.formatter io) hooks gs
  in
  { disambiguation_state
  ; indexing_state
  ; sessions = DynArray.of_list sessions
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
  | Option.None -> false
  | Option.Some (i, c) ->
     select_session s i c;
     (* select the desired theorem within the session;
            this should be guaranteed to succeed due to the
            lookup_theorem having succeeded in this case *)
     if Bool.not (Session.select_theorem c name) then
      Error.raise_violation
         "[select_theorem] selected session does not contain the theorem";
     true

(** Gets the next state triple from the prover. *)
let next_substate (s : t) =
  match next_session s with
  | Option.None -> Error.raise_notrace No_session
  | Option.Some c ->
     match Session.next_theorem c with
     | Option.None -> Error.raise_notrace (No_theorem c)
     | Option.Some t ->
        match Theorem.next_subgoal t with
        | Option.None -> Error.raise_notrace (No_subgoal { session = c; theorem = t })
        | Option.Some g -> { session = c; theorem = t; proof_state = g }

(** Drops all state and reloads from the signature.
    Typically, this is called after serialization reflects the
    state into the signature.
    Note that the current state triple is not preserved by this
    call, and that after it, the prover may be focussing on a
    different subgoal, possibly in a different session/theorem.
    To preserve focus, combine this with `keeping_focus`. *)
let reset s : unit =
  let (all_paths, sgn') = Load.load_fresh s.sig_path in
  let disambiguation_states, _last_disambiguation_state =
    Revisit.revisit_disambiguation sgn'
  in
  let indexing_states, _last_indexing_state =
    Revisit.revisit_indexing sgn'
  in
  let gs = Holes.get_harpoon_subgoals () in
  let hooks = [run_automation s.automation_state] in
  let cs =
    recover_sessions disambiguation_states indexing_states (IO.formatter s.io) hooks gs
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
let keeping_focus s { session = c; theorem = t; proof_state = g } f =
  let curr_thm_name = Theorem.get_name t in
  let curr_sg_label = g.Comp.label in
  f ();
  if Bool.not (select_theorem s curr_thm_name) then
    Error.raise_violation
      "[reset] reloaded signature does not contain the theorem \
       we were working on";
  match
    Theorem.select_subgoal_satisfying (next_substate s).theorem
      begin fun g ->
      Whnf.conv_subgoal_path_builder g.Comp.label curr_sg_label
      end
  with
  | None ->
      Error.raise_violation
       (Format.asprintf
         "[%s] [select_subgoal_satisfying] returned [None]"
         __FUNCTION__)
  | Some _ -> ()

(** Reflects the current prover state back into the loaded signature
    file.
    You should reset the prover state after doing this by calling
    `reset`.
 *)
let save s =
  let existing_holes = Holes.get_harpoon_subgoals () in
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
    (List.last s.all_paths)
    new_mutual_rec_thmss

let automation_state s = s.automation_state

let interaction_mode s = s.stop

let save_mode s = s.save_back

let is_complete s = DynArray.length s.sessions = 0

let session_configuration_wizard s =
  let open Option in
  Session.configuration_wizard s.disambiguation_state s.indexing_state s.io
    [run_automation s.automation_state]
  $> add_session s
  |> is_some

let on_session_completed s c =
  match save_mode s with
  | `save_back -> save s; reset s
  | `no_save_back ->
     remove_current_session s

let serialize s ctg = keeping_focus s ctg (fun () -> save s; reset s)

let fmt_ppr_session_list ppf s =
  let session_list = session_list s in
  let print_list f ppf x =
    Format.pp_print_list ~pp_sep:Format.pp_print_cut f ppf x
  in
  let print_indexed_session ppf (i, c) =
    Format.fprintf ppf "%d. @[<v>%a@]"
      (i + 1)
      Session.fmt_ppr_theorem_list c
  in
  printf s "@[<v>%a@]"
    (print_list print_indexed_session) (List.index session_list)
