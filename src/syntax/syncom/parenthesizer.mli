(** Utilities for creating expression pretty-printers with minimal
    parentheses.

    @author Marc-Antoine Ouimet *)

open Support

(** {1 Handling Parentheses}

    Parentheses are re-introduced during pretty-printing using the precedence
    ordering specified in the parser. Operator associativities also need to
    be considered to avoid adding extraneous parentheses. *)

(** Module type for stateful helper printers for parenthesizing applications
    with user-defined operators. *)
module type PARENTHESIZER = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  type precedence

  (** [parenthesize_term_of_lesser_precedence] is a parenthesizing formatter
      that adds parentheses to the term if it has a strictly lesser
      precedence than that of its parent node in the AST. *)
  val parenthesize_term_of_lesser_precedence :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_term_of_lesser_than_or_equal_precedence] is a
      parenthesizing formatter that adds parentheses to the term if it has a
      lesser than or equal precedence with the precedence of its parent node
      in the AST. *)
  val parenthesize_term_of_lesser_than_or_equal_precedence :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_left_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix left-associative operator. *)
  val parenthesize_left_argument_left_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_right_argument_left_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix left-associative operator. *)
  val parenthesize_right_argument_left_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_left_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a left argument to an
      infix right-associative operator. *)
  val parenthesize_left_argument_right_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_right_argument_right_associative_operator] is a
      parenthesizing formatter for a term appearing as a right argument to an
      infix right-associative operator. *)
  val parenthesize_right_argument_right_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_argument_non_associative_operator] is a parenthesizing
      formatter for a term appearing as an argument to an infix
      non-associative operator. *)
  val parenthesize_argument_non_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_argument_prefix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a prefix operator. *)
  val parenthesize_argument_prefix_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** [parenthesize_argument_postfix_operator] is a parenthesizing formatter
      for a term appearing as an argument to a postifx operator. *)
  val parenthesize_argument_postfix_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  (** {[
        pp_application state ~indent ~guard_operator
          ~guard_operator_application ~precedence_of_applicand
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand arguments
      ]}

      pretty-prints the application of [applicand] with [arguments] as a
      juxtaposition of terms delimited by whitespaces, with minimal
      parentheses.

      This pretty-printer supports applicands having a type different from
      that of its arguments. This allows for pretty-printing LF type-level
      applications, which have LF types as applicands and LF terms as
      arguments.

      - [~guard_operator state applicand] is [`Operator operator] if
        [applicand] is an operator, and [`Operand] otherwise.
      - [~guard_operator_application state argument] is
        [`Operator_application operator] if [argument] is the application of
        an operator, [`Operator operator] if [operator] is an operator in
        forced prefix notation (which requires parentheses), and [`Operand]
        otherwise.
      - [~precedence_of_applicand state applicand] is the precedence of
        [applicand].
      - [~precedence_of_argument state argument] is the precedence of
        [argument].
      - [~pp_applicand state] is a pretty-printer for the applicand.
      - [~pp_argument state] is a pretty-printer for an argument in the
        application.
      - [~parent_precedence] is the precedence of the AST node parent to
        [applicand] and [arguments], meaning that it is the precedence of the
        application. *)
  val pp_application :
       state
    -> indent:Int.t
    -> guard_operator:
         (state -> 'applicand -> [ `Operator of Operator.t | `Operand ])
    -> guard_operator_application:
         (   state
          -> 'argument
          -> [ `Operator_application of Operator.t
             | `Operator of Operator.t
             | `Operand
             ])
    -> precedence_of_applicand:(state -> 'applicand -> precedence)
    -> precedence_of_argument:(state -> 'argument -> precedence)
    -> pp_applicand:(state -> 'applicand -> Unit.t)
    -> pp_argument:(state -> 'argument -> Unit.t)
    -> parent_precedence:precedence
    -> 'applicand
    -> 'argument List1.t
    -> Unit.t
end

module Make (Format_state : Format_state.S) (Precedence : Ord.ORD) :
  PARENTHESIZER
    with type state = Format_state.state
     and type precedence = Precedence.t
