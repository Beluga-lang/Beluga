open Support

(** The type of description for infix, prefix and postfix operators. *)
type t

(** {1 Destructors} *)

(** [arity operator] is the number of arguments [operator] is expected to be
    applied with.

    - If [fixity operator = Fixity.Prefix], then [arity operator >= 0].
    - If [fixity operator = Fixity.Infix], then [arity operator = 2].
    - If [fixity operator = Fixity.Postfix], then [arity operator = 1]. *)
val arity : t -> Int.t

(** [precedence operator] is the user-defined value for parsing the order of
    operations when operands and arguments are juxtaposed.

    If [precedence o1 < precedence o2], then [o2] precedes [o1] such that
    [a o1 b o2 c] is parsed as [a o1 (b o2 c)], where [a], [b] and [c] are
    operands. *)
val precedence : t -> Int.t

(** [fixity operator] is the fixity of [operator]. *)
val fixity : t -> Fixity.t

(** [associativity operator] is the associativity of [operator].

    - If [fixity operator = Fixity.Prefix], then
      [associativity operator = Associativity.Right_associative].
    - If [fixity operator = Fixity.Postfix], then
      [associativity operator = Associativity.Left_associative]. *)
val associativity : t -> Associativity.t

(** {1 Constructors} *)

val make_prefix : arity:Int.t -> precedence:Int.t -> t

val make_infix : associativity:Associativity.t -> precedence:Int.t -> t

val make_postfix : precedence:Int.t -> t

(** {1 Predicates} *)

(** [is_prefix operator] is [true] if and only if
    [fixity operator = Fixity.Prefix]. *)
val is_prefix : t -> Bool.t

(** [is_infix operator] is [true] if and only if
    [fixity operator = Fixity.Infix]. *)
val is_infix : t -> Bool.t

(** [is_postfix operator] is [true] if and only if
    [fixity operator = Fixity.Postfix]. *)
val is_postfix : t -> Bool.t

(** [is_nullary operator] is [true] if and only if [arity operator = 0]. *)
val is_nullary : t -> Bool.t

(** [is_unary operator] is [true] if and only if [arity operator = 1]. *)
val is_unary : t -> Bool.t

(** [is_binary operator] is [true] if and only if [arity operator = 2]. *)
val is_binary : t -> Bool.t

(** [is_left_associative operator] is [true] if and only if
    [associativity operator = Associativity.Left_associative]. *)
val is_left_associative : t -> Bool.t

(** [is_right_associative operator] is [true] if and only if
    [associativity operator = Associativity.Right_associative]. *)
val is_right_associative : t -> Bool.t

(** [is_non_associative operator] is [true] if and only if
    [associativity operator = Associativity.Non_associative]. *)
val is_non_associative : t -> Bool.t

(** {1 Instances} *)

(** Structural equality instance. That is, operators are equal if they have
    the same arity, precedence, fixity and associativity. *)
include Eq.EQ with type t := t
