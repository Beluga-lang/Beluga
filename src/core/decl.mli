(** Uniform declaration numbering for late scope-checking.

    During typechecking, we must double-check scoping for constants
    defined in the store, since an incomplete Harpoon proof may be defined
    before other declarations, and we must prevent the proof from
    referring to those later declarations.
    This module declares an abstract type of declaration numbers,
    supporting a comparison (<) interpreted as "is in scope for".
 *)

(** Abstract declaration number. *)
type t

(** Scoping check: d1 < d2 if d1 is in scope for d2.
    Scoping is transitive.
 *)
val (<) : t -> t -> bool

(** Gets the next declaration number.
    Assuming `reset` hasn't been called, we have that
    if
    d1 = next ()
    d2 = next ()
    then d1 < d2 = true.
 *)
val next : unit -> t

(** Resets the declaration counter.
    Any declaration generated before this call becomes invalid.
 *)
val reset : unit -> unit
