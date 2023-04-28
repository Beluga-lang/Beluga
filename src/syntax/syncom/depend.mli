(** Dependency annotations to parameters to dependent type functions.

    In dependent function types [Πx:A.B], either:

    + [B] depends on [x]
    + [B] may or may not depend on [x]
    + [B] does not depend on [x] (which we usually denote as [A → B])

    This data type was first introduced in the Twelf system. *)

open Support

(** The type of annotation for parameters to dependent kinds or types.

    In dependent function types [Πx:A.B], the depend annotation refers to the
    relation between [x] and [B]. *)
type t = private
  | Yes
      (** The dependent type depends on the parameter.

          In the case of dependent function types, this means that it cannot
          be an arrow. *)
  | Maybe
      (** The dependent type may or may not depend on the parameter, we just
          don't know at this point.

          In the case of dependent function types, this means that it can be
          either an arrow or a Pi-type. *)
  | No
      (** The dependent type does not depend on the parameter.

          In the case of dependent function types, this means that it is
          actually an arrow. *)

(** {1 Constructors} *)

(** [yes] is [Yes]. *)
val yes : t

(** [maybe] is [Maybe]. *)
val maybe : t

(** [no] is [No]. *)
val no : t

(** {1 Instances} *)

include Eq.EQ with type t := t
