open Support

let parenthesize pp ppf = Format.fprintf ppf "@[<2>(%a)@]" pp

type ('precedence, 'term) parenthesizing_formatter =
     ('term -> 'precedence)
  -> parent_precedence:'precedence
  -> (Format.formatter -> 'term -> Unit.t)
  -> Format.formatter
  -> 'term
  -> Unit.t

module Make_parenthesizer (Precedence : Ord.ORD) = struct
  let[@inline] parenthesize_term_of_lesser_precedence precedence
      ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument < parent_precedence) then
      parenthesize pp ppf argument
    else pp ppf argument

  let[@inline] parenthesize_term_of_lesser_than_or_equal_precedence
      precedence ~parent_precedence pp ppf argument =
    if Precedence.(precedence argument <= parent_precedence) then
      parenthesize pp ppf argument
    else pp ppf argument

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

  let rec pp_application ~guard_operator ~guard_operator_application
      ~precedence_of_applicand ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence ppf (applicand, arguments) =
    match guard_operator applicand with
    | `Term ->
      (* The applicand is not an unquoted operator, so the application is in
         prefix notation. *)
      Format.fprintf ppf "@[<2>%a@ %a@]"
        (parenthesize_term_of_lesser_than_or_equal_precedence
           precedence_of_applicand ~parent_precedence pp_applicand)
        applicand
        (List1.pp ~pp_sep:Format.pp_print_space
           (parenthesize_term_of_lesser_than_or_equal_precedence
              precedence_of_argument ~parent_precedence pp_argument))
        arguments
    | `Operator operator ->
      (* The applicand is an unquoted operator, so pretty-printing must
         handle the operator fixity, associativity and precedence. *)
      pp_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand operator arguments ppf

  and pp_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator arguments ppf =
    match Operator.fixity operator with
    | Fixity.Prefix ->
      pp_prefix_operator_application ~precedence_of_argument ~pp_applicand
        ~pp_argument ~parent_precedence applicand arguments ppf
    | Fixity.Infix ->
      assert (
        List1.compare_length_with arguments 2
        = 0 (* The arguments list must have exactly two elements *));
      let[@warning "-8"] (List1.T (left_argument, [ right_argument ])) =
        arguments
      in
      pp_infix_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand operator ~left_argument ~right_argument ppf
    | Fixity.Postfix ->
      assert (
        List1.compare_length_with arguments 1
        = 0 (* The arguments list must have exactly one element *));
      let[@warning "-8"] (List1.T (argument, [])) = arguments in
      pp_postfix_operator_application ~guard_operator_application
        ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
        applicand argument ppf

  and pp_prefix_operator_application ~precedence_of_argument ~pp_applicand
      ~pp_argument ~parent_precedence applicand arguments ppf =
    Format.fprintf ppf "@[<2>%a@ %a@]" pp_applicand applicand
      (List1.pp ~pp_sep:Format.pp_print_space
         (parenthesize_argument_prefix_operator precedence_of_argument
            ~parent_precedence pp_argument))
      arguments

  and pp_postfix_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand argument ppf =
    Format.fprintf ppf "@[<2>%a@ %a@]"
      (pp_postfix_operator_argument ~guard_operator_application
         ~precedence_of_argument ~pp_argument ~parent_precedence)
      argument pp_applicand applicand

  and pp_infix_operator_application ~guard_operator_application
      ~precedence_of_argument ~pp_applicand ~pp_argument ~parent_precedence
      applicand operator ~left_argument ~right_argument ppf =
    match Operator.associativity operator with
    | Associativity.Left_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_left_associative_operator_left_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        left_argument pp_applicand applicand
        (pp_infix_left_associative_operator_right_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Right_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_right_associative_operator_left_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        left_argument pp_applicand applicand
        (pp_infix_right_associative_operator_right_argument
           ~guard_operator_application ~precedence_of_argument ~pp_argument
           ~parent_precedence operator)
        right_argument
    | Associativity.Non_associative ->
      Format.fprintf ppf "@[<2>%a@ %a@ %a@]"
        (pp_infix_non_associative_operator_left_argument
           ~precedence_of_argument ~pp_argument ~parent_precedence)
        left_argument pp_applicand applicand
        (pp_infix_non_associative_operator_right_argument
           ~precedence_of_argument ~pp_argument ~parent_precedence)
        right_argument

  and pp_infix_left_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf left_argument =
    match guard_operator_application left_argument with
    | `Term ->
      parenthesize_left_argument_left_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        left_argument
    | `Operator_application left_argument_operator ->
      if
        Operator.is_right_associative left_argument_operator
        && Operator.precedence left_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf left_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_left_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          left_argument

  and pp_infix_left_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf right_argument =
    match guard_operator_application right_argument with
    | `Term ->
      parenthesize_right_argument_left_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        right_argument
    | `Operator_application right_argument_operator ->
      if
        Operator.is_right_associative right_argument_operator
        && Operator.precedence right_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf right_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_right_argument_left_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          right_argument

  and pp_infix_right_associative_operator_left_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf left_argument =
    match guard_operator_application left_argument with
    | `Term ->
      parenthesize_left_argument_right_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        left_argument
    | `Operator_application left_argument_operator ->
      if
        Operator.is_left_associative left_argument_operator
        && Operator.precedence left_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf left_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_left_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          left_argument

  and pp_infix_right_associative_operator_right_argument
      ~guard_operator_application ~precedence_of_argument ~pp_argument
      ~parent_precedence applicand_operator ppf right_argument =
    match guard_operator_application right_argument with
    | `Term ->
      parenthesize_right_argument_right_associative_operator
        precedence_of_argument ~parent_precedence pp_argument ppf
        right_argument
    | `Operator_application right_argument_operator ->
      if
        Operator.is_left_associative right_argument_operator
        && Operator.precedence right_argument_operator
           = Operator.precedence applicand_operator
      then (parenthesize pp_argument) ppf right_argument
        (* The applications of left and right-associative operators of the
           same precedence must be parenthesized, otherwise the expression is
           ambiguous. *)
      else
        parenthesize_right_argument_right_associative_operator
          precedence_of_argument ~parent_precedence pp_argument ppf
          right_argument

  and pp_infix_non_associative_operator_left_argument ~precedence_of_argument
      ~pp_argument ~parent_precedence ppf left_argument =
    parenthesize_argument_non_associative_operator precedence_of_argument
      ~parent_precedence pp_argument ppf left_argument

  and pp_infix_non_associative_operator_right_argument
      ~precedence_of_argument ~pp_argument ~parent_precedence ppf
      right_argument =
    parenthesize_argument_non_associative_operator precedence_of_argument
      ~parent_precedence pp_argument ppf right_argument

  and pp_postfix_operator_argument ~guard_operator_application
      ~precedence_of_argument ~pp_argument ~parent_precedence ppf argument =
    match guard_operator_application argument with
    | `Term ->
      parenthesize_argument_postfix_operator precedence_of_argument
        ~parent_precedence pp_argument ppf argument
    | `Operator_application operator ->
      if Operator.is_postfix operator then pp_argument ppf argument
      else
        parenthesize_argument_postfix_operator precedence_of_argument
          ~parent_precedence pp_argument ppf argument
end
