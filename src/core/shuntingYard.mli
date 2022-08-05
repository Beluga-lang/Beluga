open Support

(** [Make (Operand) (Operator) (Writer)] is a module implementing Dijkstra's
    shunting yard algorithm for rewriting lists of [Operand.t] to an
    [Operand.t] with dynamic (or user-defined) operators.

    This implementation supports:

    - prefix operators of arbitrary fixity
    - left-associative, right-associative and non-associative infix operators
    - postfix operators of arbitrary fixity *)
module Make (Operand : sig
  (** The type of expressions to rewrite. *)
  type t
end) (Operator : sig
  (** The type of operator descriptors. *)
  type t

  (** {1 Destructors} *)

  (** [arity operator] is the number of arguments expected for [operator].

      - [arity operator >= 0].
      - If [operator] is an infix operator, then [arity operator = 2]. *)
  val arity : t -> Int.t

  (** [precedence operator] is the order of operation value for [operator].

      - If [precedence o1 < precedence o2], then [o2] precedes [o1] such that
        [a o1 b o2 c] is rewritten to [a o1 (b o2 c)], where [a], [b] and [c]
        are operands. *)
  val precedence : t -> Int.t

  (** [fixity operator] is the fixity of [operator]. *)
  val fixity : t -> Fixity.t

  (** [associativity operator] is the associativity of [operator].

      - If [fixity operator] is [Fixity.Prefix], then
        [associativity operator] is [Associativity.Right_associative].
      - If [fixity operator] is [Fixity.Postfix], then
        [associativity operator] is [Associativity.Left_associative]. *)
  val associativity : t -> Associativity.t

  (** {1 Instances} *)

  (** Instance of equality such that [equal a b = true] if and only if [a]
      and [b] refer to the same operator. The arity, precedence, fixity and
      associativity of an operator is not sufficient to distinguish different
      operators.

      This is used to determine whether non-associative operators appear
      consecutively during rewriting of an expression list. *)
  include Eq.EQ with type t := t
end) (_ : sig
  val write : Operator.t -> Operand.t List.t -> Operand.t
end) : sig
  (** The type of [Operand.t] tagged as either an operand or an operator. *)
  type primitive

  (** {1 Constructors} *)

  val operand : Operand.t -> primitive

  val operator : Operator.t -> primitive

  (** {1 Rewriting} *)

  exception Empty_expression

  exception Misplaced_operator of Operator.t * Operand.t List.t

  exception Consecutive_non_associative_operators of Operator.t * Operator.t

  exception Arity_mismatch of Operator.t * Operand.t List.t

  exception Leftover_expressions of Operand.t List2.t

  (** [shunting_yard primitives] is the result of rewriting [primitives] into
      a single operand, accounting for operator arity, precedence, fixity and
      associativity using Dijkstra's shunting yard algorithm.

      @raise [Empty_expression]
        if [primitive] is [\[\]].
      @raise [Misplaced_operator (operator, arguments)]
        if [operator] appears in an illegal position in [primitives] such that
        it would be rewriten with arguments [arguments].
      @raise [Consecutive_non_associative_operators (operator1, operator2)]
        if non-associative operator [operator2] appears in an illegal position
        in [primitives] with respect to [operator1], such that
        [operator1 = operator2], and [operator1] and [operator2] would be
        rewriten as being consecutively, as in [a operator1 b operator c].
      @raise [Arity_mismatch (operator, arguments)]
        if [operator] appears in an illegal position in [primitives] such that
        it is applied to too few arguments [arguments].
      @raise [Leftover_expressions (List2.T (o1, o2, os))]
        if operands [o2 :: os] could not be reduced further, either because an
        operator is missing, or too many arguments were supplied to an
        operator.
      *)
  val shunting_yard : primitive List.t -> Operand.t
end
