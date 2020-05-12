(** A Harpoon session represents a set of mutually proven theorems. *)

open Beluga
open Syntax.Int

module CompS = Store.Cid.Comp

type t

(** Construct a new session representing the given mutual group.

    Requirement: the mutual group identified by the given cid must
    indeed contain every given theorem. *)
val make : Id.cid_mutual_group -> Theorem.t list -> t

(** Retrieves the mutual declarations associated to this session's
    mutual group. *)
val get_mutual_decs : t -> Comp.total_dec list

(** Looks up an incomplete theorem by name in the session. *)
val lookup_theorem : t -> Id.name -> Theorem.t option

(** Gets the list of all complete and incomplete theorems in this
    session. *)
val full_theorem_list : t -> Theorem.t list

(** Moves the current theorem from the incomplete theorem stack to
    the finished theorem stack, and associates it to the given
    checkable term that is its translation.
 *)
val mark_current_theorem_as_proven : t -> Comp.exp_chk option -> unit

(** Moves the current theorem to the bottom of the incomplete theorem
    stack, selecting the next one. *)
val defer_theorem : t -> unit

(** Gets the currently focused theorem, if any.
    This returns None when all theorems in the session are complete.
 *)
val next_theorem : t -> Theorem.t option

(** Decides what kind of invocation the given synthesizable expression
    represents.
    The implementation is quite naive about detecting recursive calls,
    and will only find one in an application head position.
 *)
val infer_invocation_kind : t -> Comp.exp_syn -> Comp.invoke_kind

(** Selects a given theorem by name in the session, moving it to the
    top of the incomplete theorem stack.
    Returns whether the selection succeeded.
    Selection fails only when there is no incomplete theorem by the
    given name.
 *)
val select_theorem : t -> Id.name -> bool

(** Decides what kind of session this is.
    `introduced: this session was created within Harpoon, via the
                 session configuration wizard.
    `loaded: this session was recovered from a signature.
 *)
val get_session_kind : t -> [ `introduced | `loaded ]

(** Represents the result of trying to typecheck the translated
    proofs. *)
type translation_check_result =
  [ `some_translations_failed
  (** Returned when some theorems could not be translated.
      The user should already have seen an error indicating the
      failure. *)

  | `check_error of exn
  (** Returned when a translated theorem fails to typecheck. *)

  | `ok (** Returned on successful typechecking. *)
  ]

(** Typechecks all translated proofs in the session.
    Proofs are translated as soon as they are completed, and they are
    recorded inside the session.
    Once all proofs are completed, this function should be called to
    verify that the translation was correct.
    In principle, any proof that successfully completes should pass
    translation, and any translated proof should pass typechecking, so
    it is never a user-error if translation fails or if typechecking a
    translated proof fails.
 *)
val check_translated_proofs : t -> translation_check_result

(** Performs a series of prompts to interactively construct a new
    session. Returns None if the user aborts the session
    configuration. Otherwise, returns the newly defined session.
 *)
val configuration_wizard : IO.t -> (Theorem.t -> unit Theorem.subgoal_hook) list -> t option

(** Prints a vertical, enumerated list of all theorems in this
    session.
 *)
val fmt_ppr_theorem_list : Format.formatter -> t -> unit

(** Assigns a declaration number to all theorems in this session.
    This has the effect of making the theorems visible to other
    incomplete theorems.
    Precondition: all theorems in the session must be complete.

    Normally, this should be called right before the session is
    removed.
    It's unnecessary to call this when running in save-back mode, as
    saving the theorems and reloading the signature has the effect of
    physically materializing them in the file.
    The materialization performed by this function is virtual.
 *)
val materialize_theorems : t -> unit
