open Beluga
open Syntax.Int.Comp

module CompS = Store.Cid.Comp

module Conf : sig
  type t
  val make : Id.name -> order total_dec_kind -> typ -> int -> t
end

module Action : sig
  (** Abstract actions that can be executed forwards and backwards on
      a theorem. *)
  type t

  (** An action describes a diff on the subgoals of the theorem.
      - In the forward direction, it assigns the solution to the
        target subgoal, removes the target, and adds all child
        subgoals.
      - In the backward direction, it removes all child subgoals, adds
        the target, and clears the solution of the target.
   *)
  val make : proof_state -> (* the target subgoal *)
             proof_state list -> (* the child subgoals *)
             proof -> (* the solution *)
             t
end

module Direction : sig
  type t

  val forward : t
  val backward : t
end

type t
type theorem = t

type 'a subgoal_hook = proof_state -> 'a

(**
   TODO
   hide this from outside of this module
 *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

(** Gets the cid and Store entry for this theorem. *)
val get_entry' : t -> Id.cid_prog * CompS.Entry.t

(** Gets the Store entry for this theorem. *)
val get_entry : t -> CompS.Entry.t
val get_name : t -> Id.name
val has_name_of : t -> Id.name -> bool
val has_cid_of : t -> Id.cid_prog -> bool
val theorem_statement : t -> tclo

val serialize : Format.formatter -> t -> unit

val next_subgoal : t -> proof_state option
val select_subgoal_satisfying : t -> (proof_state -> bool) -> proof_state option
val dump_proof : Format.formatter -> t -> unit
val show_proof : t -> unit
val show_subgoals : t -> unit
val defer_subgoal : t -> unit

val subgoals : t -> proof_state list

val count_subgoals : t -> int

(** Executes the given action on this theorem, and records the action
    to the theorem's history. *)
val apply : t -> Action.t -> unit

(** Inverts the last action recorded in the history.
    Returns false if the history is empty and no action can be
    inverted. *)
val history_step : t -> Direction.t -> bool

(** Replaces the subgoal with another, solving it by transforming an
    incomplete proof for the new subgoal.
    Interally this uses `apply` and so records theorem history.
 *)
val apply_subgoal_replacement : t -> proof_state -> (proof -> proof) -> proof_state -> unit

(** Renames the given variable at the given level.
    Returns true iff such a variable could be renamed.
    Else, there was no such variable.
 *)
val rename_variable : Id.name -> Id.name -> [ `comp | `meta ] -> t -> proof_state -> bool

val configure : Id.cid_comp_const -> Format.formatter -> (t -> unit subgoal_hook) list ->
                proof_state -> proof_state list -> t
val configure_set : Format.formatter -> (t -> unit subgoal_hook) list -> Conf.t list ->
                    Id.cid_mutual_group * t list
val set_hidden : t -> bool -> unit

type completeness =
  [ `incomplete
  | `complete
  ]

(** Decides whether the theorem is complete. *)
val completeness : t -> completeness
