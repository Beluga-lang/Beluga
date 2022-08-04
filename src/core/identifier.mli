(** Plain identifiers.

    These are totally ordered for efficient lookups in map data structures. *)
open Support

type t

(** {1 Constructors} *)

val make : location:Location.t -> String.t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val name : t -> String.t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Ord.ORD with type t := t
