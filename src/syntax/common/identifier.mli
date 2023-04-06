(** String identifiers.

    An identifier is a string with a location. The string may contain a ['#']
    prefix for parameter variables or a ['$'] prefix for substitution
    variables.

    Identifiers are totally ordered for efficient lookups in map data
    structures.

    For identifiers prefixed by modules, see {!Qualified_identifier}. *)

open Support

type t

(** {1 Constructors} *)

val make : ?location:Location.t -> String.t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val name : t -> String.t

(** {1 Exceptions} *)

exception Unbound_identifier of t

(** {1 Collections} *)

module Set : Set.S with type elt = t

module Map : Map.S with type key = t

module Hamt : Hamt.S with type key = t

module Hashtbl : Hashtbl.S with type key = t

(** {1 Lists} *)

val find_duplicates : t List.t -> (t * t List2.t) List1.t Option.t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Ord.ORD with type t := t

include Show.SHOW with type t := t
