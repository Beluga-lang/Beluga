open Support

module type PARENTHESIZER = sig
  include Imperative_state.IMPERATIVE_STATE

  type precedence

  val parenthesize_term_of_lesser_precedence :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_term_of_lesser_than_or_equal_precedence :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_left_argument_left_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_right_argument_left_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_left_argument_right_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_right_argument_right_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_argument_non_associative_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_argument_prefix_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

  val parenthesize_argument_postfix_operator :
       state
    -> (state -> 'a -> precedence)
    -> parent_precedence:precedence
    -> (state -> 'a -> Unit.t)
    -> 'a
    -> Unit.t

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

module Make (Format_state : Format_state.S) (Precedence : Ord.ORD) = struct
  include Format_state

  type precedence = Precedence.t

  let left_parenthesis state = pp_char state '('

  let right_parenthesis state = pp_char state ')'

  let parenthesize state ppv v =
    left_parenthesis state;
    ppv state v;
    right_parenthesis state

  let[@inline] parenthesize_term_of_lesser_precedence state get_precedence
      ~parent_precedence pp_argument argument =
    let precedence = get_precedence state argument in
    if Precedence.(precedence < parent_precedence) then
      parenthesize state pp_argument argument
    else pp_argument state argument

  let[@inline] parenthesize_term_of_lesser_than_or_equal_precedence state
      get_precedence ~parent_precedence pp_argument argument =
    let precedence = get_precedence state argument in
    if Precedence.(precedence <= parent_precedence) then
      parenthesize state pp_argument argument
    else pp_argument state argument

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

  let rec pp_application state ~indent ~guard_operator
      ~guard_operator_application ~precedence_of_applicand
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand arguments =
    match guard_operator state applicand with
    | `Operand ->
        (* The applicand is not a user-defined operator, so the application
           is in prefix notation. *)
        let pp_applicand state =
          parenthesize_term_of_lesser_than_or_equal_precedence state
            precedence_of_applicand ~parent_precedence pp_applicand applicand
        in
        pp_hovbox state ~indent (fun state ->
            pp_applicand state;
            pp_space state;
            pp_list1 state ~sep:pp_space
              (fun state ->
                pp_prefix_operator_argument state ~guard_operator_application
                  precedence_of_argument ~parent_precedence pp_argument)
              arguments)
    | `Operator operator ->
        (* The applicand is a user-defined operator, so pretty-printing must
           handle the operator fixity, associativity and precedence. *)
        pp_operator_application state ~indent ~guard_operator_application
          ~precedence_of_argument ~pp_applicand ~pp_argument
          ~parent_precedence applicand operator arguments

  and pp_operator_application state ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator arguments =
    match Operator.fixity operator with
    | Fixity.Prefix ->
        pp_prefix_operator_application state ~indent
          ~guard_operator_application ~precedence_of_argument ~pp_applicand
          ~pp_argument ~parent_precedence applicand arguments
    | Fixity.Infix ->
        assert (
          List1.compare_length_with arguments 2
          = 0 (* The arguments list must have exactly two elements *));
        let[@warning "-8"] (List1.T (left_argument, [ right_argument ])) =
          arguments
        in
        pp_infix_operator_application state ~indent
          ~guard_operator_application ~precedence_of_argument ~pp_applicand
          ~pp_argument ~parent_precedence applicand operator ~left_argument
          ~right_argument
    | Fixity.Postfix ->
        assert (
          List1.compare_length_with arguments 1
          = 0 (* The arguments list must have exactly one element *));
        let[@warning "-8"] (List1.T (argument, [])) = arguments in
        pp_postfix_operator_application state ~indent
          ~guard_operator_application ~precedence_of_argument ~pp_applicand
          ~pp_argument ~parent_precedence applicand argument

  and pp_prefix_operator_application state ~indent
      ~guard_operator_application ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence applicand arguments =
    pp_hovbox state ~indent (fun state ->
        pp_applicand state applicand;
        pp_space state;
        pp_list1 state ~sep:pp_space
          (fun state ->
            pp_prefix_operator_argument state ~guard_operator_application
              precedence_of_argument ~parent_precedence pp_argument)
          arguments)

  and pp_prefix_operator_argument state ~guard_operator_application
      precedence_of_argument ~parent_precedence pp_argument argument =
    match guard_operator_application state argument with
    | `Operator _ -> parenthesize state pp_argument argument
    | _ ->
        parenthesize_argument_prefix_operator state precedence_of_argument
          ~parent_precedence pp_argument argument

  and pp_postfix_operator_application state ~indent
      ~guard_operator_application ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence applicand argument =
    pp_hovbox state ~indent (fun state ->
        pp_postfix_operator_argument state ~guard_operator_application
          ~precedence_of_argument ~pp_argument ~parent_precedence argument;
        pp_space state;
        pp_applicand state applicand)

  and pp_infix_operator_application state ~indent ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator ~left_argument ~right_argument =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
        let pp_left_argument state =
          pp_infix_left_associative_operator_left_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator left_argument
        in
        let pp_right_argument state =
          pp_infix_left_associative_operator_right_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator right_argument
        in
        pp_hovbox state ~indent (fun state ->
            pp_left_argument state;
            pp_space state;
            pp_applicand state applicand;
            pp_space state;
            pp_right_argument state)
    | Associativity.Right_associative ->
        let pp_left_argument state =
          pp_infix_right_associative_operator_left_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator left_argument
        in
        let pp_right_argument state =
          pp_infix_right_associative_operator_right_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence operator right_argument
        in
        pp_hovbox state ~indent (fun state ->
            pp_left_argument state;
            pp_space state;
            pp_applicand state applicand;
            pp_space state;
            pp_right_argument state)
    | Associativity.Non_associative ->
        let pp_left_argument state =
          pp_infix_non_associative_operator_left_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence left_argument
        in
        let pp_right_argument state =
          pp_infix_non_associative_operator_right_argument state
            ~guard_operator_application ~precedence_of_argument ~pp_argument
            ~parent_precedence right_argument
        in
        pp_hovbox state ~indent (fun state ->
            pp_left_argument state;
            pp_space state;
            pp_applicand state applicand;
            pp_space state;
            pp_right_argument state)

  and pp_infix_left_associative_operator_left_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator left_argument =
    match guard_operator_application state left_argument with
    | `Operand ->
        parenthesize_left_argument_left_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument left_argument
    | `Operator _ -> parenthesize state pp_argument left_argument
    | `Operator_application left_argument_operator ->
        if
          Operator.precedence left_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_left_associative left_argument_operator)
        then parenthesize state pp_argument left_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_left_argument_left_associative_operator state
            precedence_of_argument ~parent_precedence pp_argument
            left_argument

  and pp_infix_left_associative_operator_right_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator right_argument =
    match guard_operator_application state right_argument with
    | `Operand ->
        parenthesize_right_argument_left_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument
          right_argument
    | `Operator _ -> parenthesize state pp_argument right_argument
    | `Operator_application right_argument_operator ->
        if
          Operator.precedence right_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_left_associative right_argument_operator)
        then parenthesize state pp_argument right_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_right_argument_left_associative_operator state
            precedence_of_argument ~parent_precedence pp_argument
            right_argument

  and pp_infix_right_associative_operator_left_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator left_argument =
    match guard_operator_application state left_argument with
    | `Operand ->
        parenthesize_left_argument_right_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument left_argument
    | `Operator _ -> parenthesize state pp_argument left_argument
    | `Operator_application left_argument_operator ->
        if
          Operator.precedence left_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_right_associative left_argument_operator)
        then parenthesize state pp_argument left_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_left_argument_right_associative_operator state
            precedence_of_argument ~parent_precedence pp_argument
            left_argument

  and pp_infix_right_associative_operator_right_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator right_argument =
    match guard_operator_application state right_argument with
    | `Operand ->
        parenthesize_right_argument_right_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument
          right_argument
    | `Operator _ -> parenthesize state pp_argument right_argument
    | `Operator_application right_argument_operator ->
        if
          Operator.precedence right_argument_operator
          = Operator.precedence applicand_operator
          && Bool.not (Operator.is_right_associative right_argument_operator)
        then parenthesize state pp_argument right_argument
          (* The applications of left and right-associative operators of the
             same precedence must be parenthesized, otherwise the expression
             is ambiguous. *)
        else
          parenthesize_right_argument_right_associative_operator state
            precedence_of_argument ~parent_precedence pp_argument
            right_argument

  and pp_infix_non_associative_operator_left_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence left_argument =
    match guard_operator_application state left_argument with
    | `Operator _ -> parenthesize state pp_argument left_argument
    | `Operand
    | `Operator_application _ ->
        parenthesize_argument_non_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument left_argument

  and pp_infix_non_associative_operator_right_argument state
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence right_argument =
    match guard_operator_application state right_argument with
    | `Operator _ -> parenthesize state pp_argument right_argument
    | `Operand
    | `Operator_application _ ->
        parenthesize_argument_non_associative_operator state
          precedence_of_argument ~parent_precedence pp_argument
          right_argument

  and pp_postfix_operator_argument state ~guard_operator_application
      ~precedence_of_argument ~pp_argument ~parent_precedence argument =
    match guard_operator_application state argument with
    | `Operand ->
        parenthesize_argument_postfix_operator state precedence_of_argument
          ~parent_precedence pp_argument argument
    | `Operator _ -> parenthesize state pp_argument argument
    | `Operator_application operator ->
        if Operator.is_postfix operator then pp_argument state argument
        else
          parenthesize_argument_postfix_operator state precedence_of_argument
            ~parent_precedence pp_argument argument
end
