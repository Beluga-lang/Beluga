type name =
  | Anonymous
  | Named of string

type t

val of_int : int -> t
val string_of_hole_id : t -> string

(** Construct a counter for hole id numbers.
    The reason this is wrapped in a dummy functor is that functor
    instantiation allows the get_next_key function to operate on a
    private integer reference, that can be made inaccessible outside
    of holes.ml
 *)
module Make () : sig
  (** Generates the next hole ID. *)
  val next : unit -> t
end

(** Converts an option type to a name. *)
val name_of_option : string option -> name

(** Converts a name to an option type. *)
val option_of_name : name -> string option

(** Stringifies a hole name.
 * If the hole is anonymous, then its name is the empty string. *)
val string_of_name : name -> string

(** Stringifies a hole name.
 * If the hole is anonymous, then use its hole id. *)
val string_of_name_or_id : name * t -> string

(** Decides whether a hole name is anonymous. *)
val is_anonymous : name -> bool

val fmt_ppr_name : Format.formatter -> name -> unit
val fmt_ppr_id : Format.formatter -> t -> unit

val compare : t -> t -> int
