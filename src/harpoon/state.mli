open Support
open Syntax
open Syntax.Int

type t

type triple = Session.t * Theorem.t * Comp.proof_state

type triple_error =
  [ `no_session
  | `no_theorem of Session.t
  | `no_subgoal of Session.t * Theorem.t
  ]

type triple_status = (triple_error, triple) Either.t

val make : Options.save_mode -> Options.interaction_mode ->
           string -> string list ->
           IO.t ->
           Comp.open_subgoal list ->
           t

(** Wraps {!IO.parsed_prompt}. *)
val parsed_prompt : t -> ?source : string -> string -> string option -> 'a Beluga.Parser.t -> 'a

(** Prints a message to the user. *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

(** Gets a list of all sessions in the prover. *)
val session_list : t -> Session.t list

(** Moves the current session to the bottom of the session stack,
    selecting the next one. *)
val defer_session : t -> unit

(** Configures a new session interactively and adds it to the state.
    Returns whether the new session was indeed added.
    A session is not added when the user aborts the configuration process.
 *)
val session_configuration_wizard : t -> bool

val select_theorem : t -> Id.name -> bool

val automation_state : t -> Automation.State.t

(** Gets the interaction mode of the prover. *)
val interaction_mode : t -> Options.interaction_mode

val next_triple : t -> triple_status

(** Decides whether there are any sessions in the theorem. *)
val completeness : t -> [ `complete | `incomplete ]

(** To be called by the REPL when a session is completed.
    This function analyzes the current save_mode and proceeds
    accordingly.
 *)
val on_session_completed : t -> Session.t -> unit

(** Serializes the current state back to the loaded signature,
    preserving prover focus on the given state triple. *)
val serialize : t -> triple -> unit

(** Prints a vertical, enumerated list of all sessions in this state,
    together with every theorem within each session. *)
val fmt_ppr_session_list : Format.formatter -> t -> unit
