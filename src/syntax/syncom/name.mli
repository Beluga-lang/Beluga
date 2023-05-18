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

val get_modules : t -> string list

(** Generate a blank name (underscore). *)
val mk_blank : Location.t option -> t

val inc_hint_cnt : int option -> int option

val gen_fresh_name : t list -> t -> t

(** Retrieves the location of this identifier. For identifiers generated
    internally, this will be a ghost. *)
val location : t -> Location.t

(** Finds the maximum number used for the given name hint in the given
    context. Returns None if the name hint is unused. *)
val max_usage : t list -> string -> max_usage

(** Change the number of a variable. *)
val modify_number : (int option -> int option) -> t -> t

(** [mk_bvar_name vGen_opt] generates a fresh name for an LF-bound variable. *)
val mk_bvar_name : (unit -> string) option -> t

(** [mk_mvar_name vGen_opt] generates a fresh name for a meta-variable. *)
val mk_mvar_name : (unit -> string) option -> t

(** [mk_svar_name vGen_opt] generates a fresh name for a substitution
    variable. *)
val mk_svar_name : (unit -> string) option -> t

(** [mk_pvar_name vGen_opt] generates a fresh name for a parameter variable. *)
val mk_pvar_name : (unit -> string) option -> t

(** [mk_no_name ()] generates a fresh name. *)
val mk_no_name : unit -> t

(** [mk_some_name name] generates a fresh name derived from [name]. *)
val mk_some_name : t -> t

(** [mk_some_name s] generates a fresh name derived from [s]. *)
val mk_some_string : string -> t

(** [make_from_identifier identifier] constructs a name from [identifier].
    This should be deprecated once the [Name] module is fully replaced with
    [Identifier] and [Qualified_identifier]. *)
val make_from_identifier : Identifier.t -> t

(** [make_from_qualified_identifier identifier] constructs a name from
    [identifier]. This should be deprecated once the [Name] module is fully
    replaced with [Identifier] and [Qualified_identifier]. *)
val make_from_qualified_identifier : Qualified_identifier.t -> t

(** [to_identifier name] is [name] as an [Identifier.t].

    It is assumed that [get_module name = \[\]]. *)
val to_identifier : t -> Identifier.t

val string_of_name : t -> string

(** Prints a list of space-separated names. This printer does not open a box! *)
val pp_list : Format.formatter -> t list -> unit

(** {1 Instances} *)

(** Decide whether two names represent the same thing. This simply compares
    the string representations of the names. This corresponds with a user's
    intuition about when names are equal, and ignores all name generation
    hinting built in to the [t] type. *)
include Eq.EQ with type t := t

include Show.SHOW with type t := t

include Hash.HASH with type t := t
