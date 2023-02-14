include module type of Stdlib.Int

(** {1 Constructors} *)

(** Alias of {!Stdlib.int_of_string}. *)
val of_string : string -> t

(** Alias of {!Stdlib.int_of_string_opt}. *)
val of_string_opt : string -> t option

(** {1 Collections} *)

module Set : Set.S with type elt = t

module Map : Map.S with type key = t

module Hamt : HamtExt.S with type key = t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Ord.ORD with type t := t

include Hash.HASH with type t := t

include Show.SHOW with type t := t
