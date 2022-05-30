(** The type of annotation for implicit or explicit parameters.

    A parameter is implicit if

    - it was specified by the user as [(g : ctx)] in the external syntax, or
    - it was generated during reconstruction.

    A parameter is explicit if it was specified by the user as [{g : ctx}] in
    the external syntax. *)
type t = private
  | Implicit  (** The annotation for implicit parameters. *)
  | Explicit  (** The annotation for explicit parameters. *)

(** {1 Constructors} *)

(** [implicit] is [Implicit]. *)
val implicit : t

(** [explicit] is [Explicit]. *)
val explicit : t

(** {1 Predicates and comparisons} *)

(** [max p1 p2] is [Explicit] if at least one of [p1] and [p2] is [Explicit].
    Otherwise, [Implicit] is returned. *)
val max : t -> t -> t

(** [is_explicit p] is [true] if and only if [p] is [Explicit]. *)
val is_explicit : t -> bool

(** [is_implicit p] is [true] if and only if [p] is [Implicit]. *)
val is_implicit : t -> bool
