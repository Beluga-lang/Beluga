open Support
open Beluga_syntax
open Synint

module Disambiguation_state =
  Beluga_parser.Disambiguation_state.Disambiguation_state

module Indexing_state = Beluga.Index_state.Indexing_state

type t

type substate =
  { session : Session.t
  ; theorem : Theorem.t
  ; proof_state : Comp.proof_state
  }

exception No_session

exception No_theorem of Session.t

exception
  No_subgoal of
    { session : Session.t
    ; theorem : Theorem.t
    }

val make :
     Disambiguation_state.state Id.Prog.Hashtbl.t * Disambiguation_state.state
  -> Indexing_state.state Id.Prog.Hashtbl.t * Indexing_state.state
  -> Options.save_mode
  -> Options.interaction_mode
  -> string
  -> string list
  -> IO.t
  -> Comp.open_subgoal list
  -> t

(** Prints a message to the user. *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

(** Gets a list of all sessions in the prover. *)
val session_list : t -> Session.t list

(** Moves the current session to the bottom of the session stack, selecting
    the next one. *)
val defer_session : t -> unit

(** Configures a new session interactively and adds it to the state. Returns
    whether the new session was indeed added. A session is not added when the
    user aborts the configuration process. *)
val session_configuration_wizard : t -> bool

val select_theorem : t -> Name.t -> bool

val automation_state : t -> Automation.State.t

(** Gets the interaction mode of the prover. *)
val interaction_mode : t -> Options.interaction_mode

val next_substate : t -> substate

(** Decides whether there are any sessions in the theorem. *)
val is_complete : t -> bool

(** To be called by the REPL when a session is completed. This function
    analyzes the current save_mode and proceeds accordingly. *)
val on_session_completed : t -> Session.t -> unit

(** Serializes the current state back to the loaded signature, preserving
    prover focus on the given state substate. *)
val serialize : t -> substate -> unit

(** Prints a vertical, enumerated list of all sessions in this state,
    together with every theorem within each session. *)
val fmt_ppr_session_list : Format.formatter -> t -> unit
