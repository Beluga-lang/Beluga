(** String identifiers.

    An identifier is a string with a location. The string may contain a ['#']
    prefix for parameter variables or a ['$'] prefix for substitution
    variables.

    Identifiers are totally ordered for efficient lookups in map data
    structures.

    For identifiers prefixed by modules, see {!QualifiedIdentifier}. *)

open Support

type t

(** {1 Constructors} *)

val make : ?location:Location.t -> String.t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val name : t -> String.t

(** {1 Collections} *)

module Set : Set.S with type elt = t

module Hamt : Hamt.S with type key = t

(** {1 Lists} *)

(** [inspect_duplicates identifiers] is [duplicates_opt, set], where
    [duplicates_opt] is the list of duplicate identifiers in [identifiers],
    and [set] is [identifiers] as a set. *)
val inspect_duplicates : t List.t -> t List2.t Option.t * Set.t

(** [find_duplicates identifiers] is
    [Pair.fst (inspect_duplicates identifiers)]. *)
val find_duplicates : t List.t -> t List2.t Option.t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Ord.ORD with type t := t

include Show.SHOW with type t := t
