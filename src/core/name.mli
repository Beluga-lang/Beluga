open Support

(** A `name' represents the original named representation of a variable.
    These are primarily used in parsing and pretty- printing. Names should
    never be constructed directly. See `mk_name'. *)
type t

(* For reporting whether a name is used in a context. *)
type max_usage =
  [ `used of int option
  | `unused
  ]

val base_name : t -> string

val get_module : t -> string list

(** Generate a blank name (underscore). *)
val mk_blank : Location.t option -> t

val inc_hint_cnt : int option -> int option

val gen_fresh_name : t list -> t -> t

val inc : t -> t

(** Retrieves the location of this identifier. For identifiers generated
    internally, this will be a ghost. *)
val loc_of_name : t -> Location.t

(** Finds the maximum number used for the given name hint in the given
    context. Returns None if the name hint is unused. *)
val max_usage : t list -> string -> max_usage

(** Change the number of a variable. *)
val modify_number : (int option -> int option) -> t -> t

type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | SVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of t
  | SomeString of string

(** Smart constructor for [t].

    [mk_name] generates a [t] with a guaranteed unique [string]. *)
val mk_name : ?loc:Location.t -> ?modules:string list -> name_guide -> t

val string_of_name : t -> string

val render_name : t -> string

(** Prints a list of space-separated names. This printer does not open a box! *)
val pp_list : Format.formatter -> t list -> unit

(** {1 Instances} *)

(** Decide whether two names represent the same thing. This simply compares
    the string representations of the names. This corresponds with a user's
    intuition about when names are equal, and ignores all name generation
    hinting built in to the [t] type. *)
include Eq.EQ with type t := t

include Show.SHOW with type t := t
