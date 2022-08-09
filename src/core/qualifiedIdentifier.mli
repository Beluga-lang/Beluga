(** Namespaced identifiers.

    These are names for referring to bound variable names nested in modules. *)

open Support

type t

(** {1 Constructors} *)

val make :
  location:Location.t -> ?modules:Identifier.t List.t -> Identifier.t -> t

val make_simple : Identifier.t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val name : t -> Identifier.t

val modules : t -> Identifier.t List.t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Show.SHOW with type t := t
