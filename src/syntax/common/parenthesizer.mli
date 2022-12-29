(** Utilities for creating expression pretty-printers with minimal
    parentheses. *)

open Support

(** {1 Handling Parentheses}

    Parentheses are re-introduced during pretty-printing using the precedence
    ordering specified in the parser. Operator associativities also need to
    be considered to avoid adding extraneous parentheses. *)

(** [parenthesize pp] is [pp] with the addition of parentheses. *)
val parenthesize :
  (Format.formatter -> 'a -> Unit.t) -> Format.formatter -> 'a -> Unit.t

(** A parenthesizing formatter is a pretty-printer for at term that performs
    an additional check to determine whether to parenthesize the term or not.
    This check is performed by computing the precedence of the term and
    comparing it with the precedence of the parent node in the AST. *)
type ('precedence, 'term) parenthesizing_formatter =
     ('term -> 'precedence)
  -> parent_precedence:'precedence
  -> (Format.formatter -> 'term -> Unit.t)
  -> Format.formatter
  -> 'term
  -> Unit.t

(** Functor for parenthesizing helper formatters. *)
module Make_parenthesizer (Precedence : Ord.ORD) : sig
  (** [parenthesize_term_of_lesser_precedence] is a parenthesizing formatter
      that adds parentheses to the term if it has a strictly lesser
      precedence than that of its parent node in the AST. *)
  val parenthesize_term_of_lesser_precedence :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_term_of_lesser_than_or_equal_precedence] is a
      parenthesizing formatter that adds parentheses to the term if it has a
      lesser than or equal precedence with the precedence of its parent node
      in the AST. *)
  val parenthesize_term_of_lesser_than_or_equal_precedence :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_left_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix left-associative operator. *)
  val parenthesize_left_argument_left_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_right_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix left-associative operator. *)
  val parenthesize_right_argument_left_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_left_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix right-associative operator. *)
  val parenthesize_left_argument_right_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_right_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix right-associative operator. *)
  val parenthesize_right_argument_right_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_non_associative_operator] is a parenthesizing
      formatter for a term appearing as an argument to an infix
      non-associative operator. *)
  val parenthesize_argument_non_associative_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_prefix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a prefix operator. *)
  val parenthesize_argument_prefix_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** [parenthesize_argument_postfix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a postifx operator. *)
  val parenthesize_argument_postfix_operator :
    (Precedence.t, 'argument) parenthesizing_formatter

  (** {[
        pp_application ~guard_operator ~guard_operator_application
          ~precedence_of_applicand ~precedence_of_argument ~pp_applicand
          ~pp_argument ~parent_precedence ppf (applicand, arguments)
      ]}

      pretty-prints the application of [applicand] with [arguments] as a
      juxtaposition of terms delimited by whitespaces, with minimal
      parentheses.

      This pretty-printer supports applicands having a type different from
      that of its arguments. This allows for pretty-printing LF type-level
      applications, which have LF types as applicands and LF terms as
      arguments.

      - [~guard_operator applicand] is [`Operator operator] if [applicand] is
        an unquoted operator, and [`Term] otherwise.
      - [~guard_operator_application argument] is
        [`Operator_application operator] if [argument] is the application of
        an unquoted operator, and [`Term] otherwise.
      - [~precedence_of_applicand applicand] is the precedence of
        [applicand].
      - [~precedence_of_argument argument] is the precedence of [argument].
      - [~pp_applicand] is a pretty-printer for the applicand.
      - [~pp_argument] is a pretty-printer for an argument in the
        application.
      - [~parent_precedence] is the precedence of the AST node parent to
        [applicand] and [arguments], meaning that it is the precedence of the
        application. *)
  val pp_application :
       guard_operator:('applicand -> [ `Term | `Operator of Operator.t ])
    -> guard_operator_application:
         ('argument -> [ `Term | `Operator_application of Operator.t ])
    -> precedence_of_applicand:('applicand -> Precedence.t)
    -> precedence_of_argument:('argument -> Precedence.t)
    -> pp_applicand:(Format.formatter -> 'applicand -> Unit.t)
    -> pp_argument:(Format.formatter -> 'argument -> Unit.t)
    -> parent_precedence:Precedence.t
    -> Format.formatter
    -> 'applicand * 'argument List1.t
    -> Unit.t
end
