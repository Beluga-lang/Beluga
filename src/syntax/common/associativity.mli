(** Description for the associativity of user-defined operators. *)

open Support

(** The type of annotation for the associativity of an infix operator.

    Let [f] be an infix operator and [a1], [a2], and [a3] be arguments. Then,

    - if [f] is left-associative, then [a1 f a2 f a3] is parsed as
      [(a1 f a2) f a3]
    - if [f] is right-associative, then [a1 f a2 f a3] is parsed as
      [a1 f (a2 f a3)]
    - if [f] is non-associative, then [a1 f a2 f a3] is a syntax error. *)
type t = private
  | Left_associative
  | Right_associative
  | Non_associative

(** {1 Constructors} *)

(** [left_associative] is [Left_associative]. *)
val left_associative : t

(** [right_associative] is [Right_associative]. *)
val right_associative : t

(** [non_associative] is [Non_associative]. *)
val non_associative : t

(** {1 Predicates and Comparisons} *)

(** [is_left_associative f] is [true] if and only if [f] is
    [Left_associative]. *)
val is_left_associative : t -> bool

(** [is_right_associative f] is [true] if and only if [f] is
    [Right_associative]. *)
val is_right_associative : t -> bool

(** [is_non_associative f] is [true] if and only if [f] is [Non_associative]. *)
val is_non_associative : t -> bool

(** {1 Instances} *)

include Eq.EQ with type t := t
