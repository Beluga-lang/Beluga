open Support

module type PARENTHESIZER = sig
  include State.STATE

  type precedence

  val parenthesize_term_of_lesser_precedence :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_term_of_lesser_than_or_equal_precedence :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_left_argument_left_associative_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_right_argument_left_associative_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_left_argument_right_associative_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_right_argument_right_associative_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_non_associative_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_prefix_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_postfix_operator :
       ('a -> precedence)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val pp_application :
       indent:Int.t
    -> guard_operator:('a -> [ `Operator of Operator.t | `Term ])
    -> guard_operator_application:
         ('b -> [ `Operator_application of Operator.t | `Term ])
    -> precedence_of_applicand:('a -> precedence)
    -> precedence_of_argument:('b -> precedence)
    -> pp_applicand:('a -> unit t)
    -> pp_argument:('b -> unit t)
    -> parent_precedence:precedence
    -> 'a * 'b List1.t
    -> unit t
end

module Make (Format_state : Format_state.S) (Precedence : Ord.ORD) :
  PARENTHESIZER
    with type state = Format_state.state
     and type precedence = Precedence.t
