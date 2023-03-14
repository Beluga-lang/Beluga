open Support

module type PARENTHESIZER = sig
  include State.STATE

  type precedence

  val parenthesize_term_of_lesser_precedence :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_term_of_lesser_than_or_equal_precedence :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_left_argument_left_associative_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_right_argument_left_associative_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_left_argument_right_associative_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_right_argument_right_associative_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_non_associative_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_prefix_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val parenthesize_argument_postfix_operator :
       ('a -> precedence t)
    -> parent_precedence:precedence
    -> ('a -> unit t)
    -> 'a
    -> unit t

  val pp_application :
       indent:Int.t
    -> guard_operator:
         ('applicand -> [ `Operator of Operator.t | `Operand ] t)
    -> guard_operator_application:
         (   'argument
          -> [ `Operator_application of Operator.t
             | `Operator of Operator.t
             | `Operand
             ]
             t)
    -> precedence_of_applicand:('applicand -> precedence t)
    -> precedence_of_argument:('argument -> precedence t)
    -> pp_applicand:('applicand -> unit t)
    -> pp_argument:('argument -> unit t)
    -> parent_precedence:precedence
    -> 'applicand
    -> 'argument List1.t
    -> unit t
end

module Make (Format_state : Format_state.S) (Precedence : Ord.ORD) :
  PARENTHESIZER
    with type state = Format_state.state
     and type precedence = Precedence.t = struct
  include Format_state

  type precedence = Precedence.t

  let left_parenthesis = pp_char '('

  let right_parenthesis = pp_char ')'

  let parenthesize ppv v = left_parenthesis ++ ppv v ++ right_parenthesis

  let[@inline] parenthesize_term_of_lesser_precedence get_precedence
      ~parent_precedence pp_argument argument =
    let* precedence = get_precedence argument in
    if Precedence.(precedence < parent_precedence) then
      parenthesize pp_argument argument
    else pp_argument argument

  let[@inline] parenthesize_term_of_lesser_than_or_equal_precedence
      get_precedence ~parent_precedence pp_argument argument =
    let* precedence = get_precedence argument in
    if Precedence.(precedence <= parent_precedence) then
      parenthesize pp_argument argument
    else pp_argument argument

  let parenthesize_left_argument_left_associative_operator =
    parenthesize_term_of_lesser_precedence

  let parenthesize_right_argument_left_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_left_argument_right_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_right_argument_right_associative_operator =
    parenthesize_term_of_lesser_precedence

  let parenthesize_argument_non_associative_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_argument_prefix_operator =
    parenthesize_term_of_lesser_than_or_equal_precedence

  let parenthesize_argument_postfix_operator =
    parenthesize_term_of_lesser_precedence

  let rec pp_application ~indent ~guard_operator ~guard_operator_application
      ~precedence_of_applicand ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence applicand arguments =
    guard_operator applicand >>= function
    | `Operand ->
        (* The applicand is not a user-defined operator, so the application
           is in prefix notation. *)
        let pp_applicand =
          parenthesize_term_of_lesser_than_or_equal_precedence
            precedence_of_applicand ~parent_precedence pp_applicand applicand
        in
        pp_hovbox ~indent
          (pp_applicand ++ pp_space
          ++ pp_list1 ~sep:pp_space
               (pp_prefix_operator_argument ~guard_operator_application
                  precedence_of_argument ~parent_precedence pp_argument)
               arguments)
    | `Operator operator ->
        (* The applicand is a user-defined operator, so pretty-printing must
           handle the operator fixity, associativity and precedence. *)
        pp_operator_application ~indent ~guard_operator_application
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand operator arguments

  and pp_operator_application ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator arguments =
    match Operator.fixity operator with
    | Fixity.Prefix ->
        pp_prefix_operator_application ~indent ~guard_operator_application
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand arguments
    | Fixity.Infix ->
        assert (
          List1.compare_length_with arguments 2
          = 0 (* The arguments list must have exactly two elements *));
        let[@warning "-8"] (List1.T (left_argument, [ right_argument ])) =
          arguments
        in
        pp_infix_operator_application ~indent ~guard_operator_application
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand operator ~left_argument
          ~right_argument
    | Fixity.Postfix ->
        assert (
          List1.compare_length_with arguments 1
          = 0 (* The arguments list must have exactly one element *));
        let[@warning "-8"] (List1.T (argument, [])) = arguments in
        pp_postfix_operator_application ~indent ~guard_operator_application
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand argument

  and pp_prefix_operator_application ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand arguments =
    pp_hovbox ~indent
      (pp_applicand applicand ++ pp_space
      ++ pp_list1 ~sep:pp_space
           (pp_prefix_operator_argument ~guard_operator_application
              precedence_of_argument ~parent_precedence pp_argument)
           arguments)

  and pp_prefix_operator_argument ~guard_operator_application
      precedence_of_argument ~parent_precedence pp_argument argument =
    guard_operator_application argument >>= function
    | `Operator _ -> parenthesize pp_argument argument
    | _ ->
        parenthesize_argument_prefix_operator precedence_of_argument
          ~parent_precedence pp_argument argument

  and pp_postfix_operator_application ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand argument =
    pp_hovbox ~indent
      (pp_postfix_operator_argument ~guard_operator_application
         ~precedence_of_argument ~pp_argument ~parent_precedence argument
      ++ pp_space ++ pp_applicand applicand)

  and pp_infix_operator_application ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator ~left_argument ~right_argument =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
        let pp_left_argument =
          pp_infix_left_associative_operator_left_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator left_argument
        in
        let pp_right_argument =
          pp_infix_left_associative_operator_right_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator right_argument
        in
        pp_hovbox ~indent
          (pp_left_argument ++ pp_space ++ pp_applicand applicand ++ pp_space
         ++ pp_right_argument)
    | Associativity.Right_associative ->
        let pp_left_argument =
          pp_infix_right_associative_operator_left_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator left_argument
        in
        let pp_right_argument =
          pp_infix_right_associative_operator_right_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator right_argument
        in
        pp_hovbox ~indent
          (pp_left_argument ++ pp_space ++ pp_applicand applicand ++ pp_space
         ++ pp_right_argument)
    | Associativity.Non_associative ->
        let pp_left_argument =
          pp_infix_non_associative_operator_left_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence left_argument
        in
        let pp_right_argument =
          pp_infix_non_associative_operator_right_argument
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence right_argument
        in
        pp_hovbox ~indent
          (pp_left_argument ++ pp_space ++ pp_applicand applicand ++ pp_space
         ++ pp_right_argument)

  and pp_infix_left_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator left_argument =
    guard_operator_application left_argument >>= function
    | `Operand ->
        parenthesize_left_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument left_argument
    | `Operator _ -> parenthesize pp_argument left_argument
    | `Operator_application left_argument_operator ->
        if
          Operator.precedence left_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_left_associative left_argument_operator)
        then (parenthesize pp_argument) left_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_left_argument_left_associative_operator
            precedence_of_argument ~parent_precedence pp_argument
            left_argument

  and pp_infix_left_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator right_argument =
    guard_operator_application right_argument >>= function
    | `Operand ->
        parenthesize_right_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument
          right_argument
    | `Operator _ -> parenthesize pp_argument right_argument
    | `Operator_application right_argument_operator ->
        if
          Operator.precedence right_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_left_associative right_argument_operator)
        then (parenthesize pp_argument) right_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_right_argument_left_associative_operator
            precedence_of_argument ~parent_precedence pp_argument
            right_argument

  and pp_infix_right_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator left_argument =
    guard_operator_application left_argument >>= function
    | `Operand ->
        parenthesize_left_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument left_argument
    | `Operator _ -> parenthesize pp_argument left_argument
    | `Operator_application left_argument_operator ->
        if
          Operator.precedence left_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_right_associative left_argument_operator)
        then (parenthesize pp_argument) left_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_left_argument_right_associative_operator
            precedence_of_argument ~parent_precedence pp_argument
            left_argument

  and pp_infix_right_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator right_argument =
    guard_operator_application right_argument >>= function
    | `Operand ->
        parenthesize_right_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument
          right_argument
    | `Operator _ -> parenthesize pp_argument right_argument
    | `Operator_application right_argument_operator ->
        if
          Operator.precedence right_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_right_associative right_argument_operator)
        then (parenthesize pp_argument) right_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_right_argument_right_associative_operator
            precedence_of_argument ~parent_precedence pp_argument
            right_argument

  and pp_infix_non_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence left_argument =
    guard_operator_application left_argument >>= function
    | `Operator _ -> parenthesize pp_argument left_argument
    | _ ->
        parenthesize_argument_non_associative_operator precedence_of_argument
          ~parent_precedence pp_argument left_argument

  and pp_infix_non_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence right_argument =
    guard_operator_application right_argument >>= function
    | `Operator _ -> parenthesize pp_argument right_argument
    | _ ->
        parenthesize_argument_non_associative_operator precedence_of_argument
          ~parent_precedence pp_argument right_argument

  and pp_postfix_operator_argument ~guard_operator_application
      ~precedence_of_argument ~pp_argument ~parent_precedence argument =
    guard_operator_application argument >>= function
    | `Operand ->
        parenthesize_argument_postfix_operator precedence_of_argument
          ~parent_precedence pp_argument argument
    | `Operator _ -> parenthesize pp_argument argument
    | `Operator_application operator ->
        if Operator.is_postfix operator then pp_argument argument
        else
          parenthesize_argument_postfix_operator precedence_of_argument
            ~parent_precedence pp_argument argument
end
