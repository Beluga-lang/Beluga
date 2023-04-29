(** Module for dealing with Harpoon proof serialization. *)

open Beluga_syntax
open Int

(** Appends mutual groups of theorems to the end of the file at the
    given path.
    Each `Theorem.t list` represents one session.
    They are appended in order.
 *)
val append_sessions : string -> Theorem.t list list -> unit

val update_existing_holes : Comp.open_subgoal list -> unit
