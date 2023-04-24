(** Description of user-defined oeprators. *)

open Support

(** The type of description for infix, prefix and postfix operators. *)
type t

(** {1 Destructors} *)

(** [arity operator] is the number of arguments [operator] is expected to be
    applied with.

    - If [fixity operator = Fixity.Prefix], then [arity operator = 1].
    - If [fixity operator = Fixity.Infix], then [arity operator = 2].
    - If [fixity operator = Fixity.Postfix], then [arity operator = 1]. *)
val arity : t -> int

(** [precedence operator] is the user-defined value for parsing the order of
    operations when operands and arguments are juxtaposed.

    If [precedence o1 < precedence o2], then [o2] precedes [o1] such that
    [a o1 b o2 c] is parsed as [a o1 (b o2 c)], where [a], [b] and [c] are
    operands. *)
val precedence : t -> int

(** [fixity operator] is the fixity of [operator]. *)
val fixity : t -> Fixity.t

(** [associativity operator] is the associativity of [operator].

    - If [fixity operator = Fixity.Prefix], then
      [associativity operator = Associativity.Right_associative].
    - If [fixity operator = Fixity.Postfix], then
      [associativity operator = Associativity.Left_associative]. *)
val associativity : t -> Associativity.t

(** {1 Constructors} *)

(** [make_prefix ~precedence] is a description for an operator with
    [~precedence]. *)
val make_prefix : precedence:int -> t

(** [make_infix ~associativity ~precedence] is a description for an operator
    with [~associativity] and [~precedence]. *)
val make_infix : associativity:Associativity.t -> precedence:int -> t

(** [make_postfix ~precedence] is a description for an operator with
    [~precedence]. *)
val make_postfix : precedence:int -> t

(** {1 Predicates} *)

(** [is_prefix operator] is [true] if and only if
    [fixity operator = Fixity.Prefix]. *)
val is_prefix : t -> bool

(** [is_infix operator] is [true] if and only if
    [fixity operator = Fixity.Infix]. *)
val is_infix : t -> bool

(** [is_postfix operator] is [true] if and only if
    [fixity operator = Fixity.Postfix]. *)
val is_postfix : t -> bool

(** [is_unary operator] is [true] if and only if [arity operator = 1]. *)
val is_unary : t -> bool

(** [is_binary operator] is [true] if and only if [arity operator = 2]. *)
val is_binary : t -> bool

(** [is_left_associative operator] is [true] if and only if
    [associativity operator = Associativity.Left_associative]. *)
val is_left_associative : t -> bool

(** [is_right_associative operator] is [true] if and only if
    [associativity operator = Associativity.Right_associative]. *)
val is_right_associative : t -> bool

(** [is_non_associative operator] is [true] if and only if
    [associativity operator = Associativity.Non_associative]. *)
val is_non_associative : t -> bool

(** {1 Instances} *)

(** Structural equality instance. That is, operators are equal if they have
    the same arity, precedence, fixity and associativity. *)
include Eq.EQ with type t := t
