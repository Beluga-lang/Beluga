(** Description for the fixity of user-defined operators. *)

open Support

(** The type of annotation for the fixity of an operator.

    Let [f] be an operator and [a], [a1], [a2] be arguments. Then,

    - if [f] is prefix, then it is called as [f a]
    - if [f] is infix, then it is called as [a1 f a2]
    - if [f] is postfix, then it is called as [a f] *)
type t = private
  | Prefix  (** The annotation for prefix operators. *)
  | Infix  (** The annotation for infix operators. *)
  | Postfix  (** The annotation for postfix operators. *)

(** {1 Constructors} *)

(** [prefix] is [Prefix]. *)
val prefix : t

(** [infix] is [Infix] *)
val infix : t

(** [postfix] is [Postfix] *)
val postfix : t

(** {1 Predicates and Comparisons} *)

(** [is_prefix f] is [true] if and only if [f] is [Prefix]. *)
val is_prefix : t -> bool

(** [is_infix f] is [true] if and only if [f] is [Infix]. *)
val is_infix : t -> bool

(** [is_postfix f] is [true] if and only if [f] is [Postfix]. *)
val is_postfix : t -> bool

(** {1 Instances} *)

include Eq.EQ with type t := t
