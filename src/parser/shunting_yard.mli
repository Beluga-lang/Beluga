(** Implementation of Dijkstra's shunting yard algorithm for parsing
    expression operators using reverse Polish notation.

    This is used for parsing terms having operators with user-defined
    precedences, fixities, and associativities.

    @author Marc-Antoine Ouimet *)

open Support

module type ASSOCIATIVITY = sig
  type t = private
    | Left_associative
    | Right_associative
    | Non_associative
end

module type FIXITY = sig
  type t = private
    | Prefix
    | Infix
    | Postfix
end

module type OPERAND = sig
  (** The type of expressions to rewrite. *)
  type t
end

module type OPERATOR = sig
  type associativity

  type fixity

  type operand

  (** The type of operator descriptors. *)
  type t

  (** {1 Destructors} *)

  (** [arity operator] is the number of arguments expected for [operator].

      - [arity operator >= 0].
      - If [operator] is an infix operator, then [arity operator = 2]. *)
  val arity : t -> int

  (** [precedence operator] is the order of operation value for [operator].

      If [precedence o1 < precedence o2], then [o2] precedes [o1] such that
      [a o1 b o2 c] is rewritten to [a o1 (b o2 c)], where [a], [b] and [c]
      are operands. *)
  val precedence : t -> int

  (** [fixity operator] is the fixity of [operator]. *)
  val fixity : t -> fixity

  (** [associativity operator] is the associativity of [operator].

      - If the operator is prefix, then it is right-associative.
      - If the operator is postifx, then it is left-associative. *)
  val associativity : t -> associativity

  (** {1 Writing} *)

  (** [write operator arguments] takes the list of arguments [arguments] and
      rewrites it to an application with head [operator] and arguments
      [arguments].

      The operands in [arguments] are in order, meaning that writing the
      prefix operator [operator a1 a2 ... an] has
      [arguments = a1 :: a2 :: ... :: an].

      Additionally, [arity operator = List.length arguments]. *)
  val write : t -> operand list -> operand

  (** {1 Instances} *)

  (** Instance of equality such that [equal a b = true] if and only if [a]
      and [b] refer to the same operator. The arity, precedence, fixity and
      associativity of an operator is not sufficient to distinguish different
      operators.

      This is used to determine whether non-associative operators appear
      consecutively during rewriting of an expression list. *)
  include Eq.EQ with type t := t
end

module type S = sig
  type operand

  type operator

  (** The type of expressions tagged as either an operand or an operator for
      rewriting with {!shunting_yard}. *)
  type primitive

  (** {1 Constructors} *)

  val operand : operand -> primitive

  val operator : operator -> primitive

  (** {1 Rewriting} *)

  (** [Empty_expression] is raised from [shunting_yard primitives] if
      [primitives = \[\]]. *)
  exception Empty_expression

  (** [Misplaced_operator { operator; operands }] is raised from
      [shunting_yard primitives] if [operator] appears in an illegal position
      in [primitives] such that it would be rewritten with arguments
      [arguments]. *)
  exception
    Misplaced_operator of
      { operator : operator
      ; operands : operand list
      }

  (** [Ambiguous_operator_placement { left_operator; right_operator }] is
      raised from [shunting_yard primitives] if [right_operator] appears in
      an illegal position in [primitives] with respect to [left_operator],
      such that [left_operator] and [right_operator] have the same
      precedence, and would be rewritten as being consecutive while one of
      [left_operator] and [right_operator] is left-associative with the other
      being right-associative.

      For instance:

      - [a -> b <- c] is ambiguous if [->] is right-associative and [<-] is
        left-associative, with [->] and [<-] having the same precedence.
      - [a <- b -> c] is ambiguous if [<-] is left-associative and [->] is
        right-associative, with [<-] and [->] having the same precedence.
      - [++ a + b] is ambiguous if [++] is right-associative and [+] is
        left-associative, with [++] and [+] having the same precedence.
      - [++ a !] is ambiguous if [++] is right-associative and [!] is
        left-associative, with [++] and [!] having the same precedence.
      - [a ^ b !] is ambiguous if [^] is right-associative and [!] is
        left-associative, with [^] and [!] having the same precedence. *)
  exception
    Ambiguous_operator_placement of
      { left_operator : operator
      ; right_operator : operator
      }

  (** [Consecutive_non_associative_operators { left_operator; right_operator }]
      is raised from [shunting_yard primitives] if non-associative operator
      [right_operator] appears in an illegal position in [primitives] with
      respect to [left_operator], such that [left_operator = right_operator],
      and [left_operator] and [right_operator] would be rewritten as being
      consecutive, as in [a left_operator b right_operator c]. *)
  exception
    Consecutive_non_associative_operators of
      { left_operator : operator
      ; right_operator : operator
      }

  (** [Arity_mismatch { operator; operator_arity; operands }] is raised from
      [shunting_yard primitives] if [operator] appears in an illegal position
      in [primitives] such that it is applied to too few arguments, meaning
      that [List.length arguments < operator_arity]. *)
  exception
    Arity_mismatch of
      { operator : operator
      ; operator_arity : int
      ; operands : operand list
      }

  (** [Leftover_expressions (List2.T (o1, o2, os))] is raised from
      [shunting_yard primitives] if operands [o2 :: os] could not be reduced
      further, either because an operator is missing, or too many arguments
      were supplied to an operator. *)
  exception Leftover_expressions of operand List2.t

  (** [shunting_yard primitives] is the result of rewriting [primitives] into
      a single operand, accounting for operator arity, precedence, fixity and
      associativity using Dijkstra's shunting yard algorithm.

      @raise Empty_expression
      @raise Misplaced_operator
      @raise Ambiguous_operator_placement
      @raise Consecutive_non_associative_operators
      @raise Arity_mismatch
      @raise Leftover_expressions *)
  val shunting_yard : primitive list -> operand
end

(** [Make (Associativity) (Fixity) (Operand) (Operator)] is a module
    implementing Dijkstra's shunting yard algorithm for rewriting lists of
    [Operand.t] to an [Operand.t] with dynamic (or user-defined) operators.

    This implementation supports:

    - prefix operators of arbitrary arity
    - left-associative, right-associative and non-associative infix operators
    - postfix operators of arbitrary arity *)
module Make
    (Associativity : ASSOCIATIVITY)
    (Fixity : FIXITY)
    (Operand : OPERAND)
    (Operator : OPERATOR
                  with type associativity = Associativity.t
                   and type fixity = Fixity.t
                   and type operand = Operand.t) :
  S with type operand = Operand.t and type operator = Operator.t
