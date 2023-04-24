open Support
open Beluga_syntax.Common

module type EXPRESSION = sig
  type t

  type location

  val location : t -> location
end

module Make_application_parser
    (Expression : EXPRESSION with type location = Location.t) =
struct
  type expression = Expression.t

  type source =
    | Expression of
        { expression : Expression.t
        ; location : Location.t
        }
    | Operator of
        { applicand : Expression.t
        ; operator : Operator.t
        ; identifier : Qualified_identifier.t
        ; location : Location.t
        }

  let make_expression expression =
    let location = Expression.location expression in
    Expression { expression; location }

  let make_operator applicand operator identifier =
    let location = Expression.location applicand in
    Operator { applicand; operator; identifier; location }

  let source_location = function
    | Expression { location; _ }
    | Operator { location; _ } ->
        location

  module State = Parser_combinator.Make_persistent_state (struct
    type t = source

    type location = Location.t

    let location = source_location
  end)

  include State
  include Parser_combinator.Make (State)

  type target =
    | Atom of
        { expression : Expression.t
        ; location : Location.t
        }
    | Application of
        { applicand : Expression.t
        ; arguments : target List1.t
        ; location : Location.t
        }

  let parse_tree_location = function
    | Atom { location; _ }
    | Application { location; _ } ->
        location

  let atom expression =
    Atom { expression; location = Expression.location expression }

  let application applicand arguments =
    let location =
      Location.join
        (Expression.location applicand)
        (Location.join
           (parse_tree_location (List1.head arguments))
           (parse_tree_location (List1.last arguments)))
    in
    Application { applicand; arguments; location }

  let prefix_application applicand argument =
    let arguments = List1.singleton argument
    and location =
      Location.join
        (Expression.location applicand)
        (parse_tree_location argument)
    in
    Application { applicand; arguments; location }

  let infix_application left_argument applicand right_argument =
    let arguments = List1.from left_argument [ right_argument ]
    and location =
      Location.join
        (parse_tree_location left_argument)
        (parse_tree_location right_argument)
    in
    Application { applicand; arguments; location }

  let postfix_application argument applicand =
    let arguments = List1.singleton argument
    and location =
      Location.join
        (Expression.location applicand)
        (parse_tree_location argument)
    in
    Application { applicand; arguments; location }

  exception Expected_expression of { actual : Expression.t Option.t }

  let expression =
    satisfy (function
      | Option.Some (Expression { expression; _ }) -> Result.ok expression
      | Option.Some (Operator { applicand; _ }) ->
          Result.error
            (Expected_expression { actual = Option.some applicand })
      | Option.None ->
          Result.error (Expected_expression { actual = Option.none }))

  exception
    Expected_operator of
      { expected : Qualified_identifier.t
      ; actual : Expression.t Option.t
      }

  let operator expected_identifier =
    satisfy (function
      | Option.Some (Expression { expression; _ }) ->
          Result.error
            (Expected_operator
               { expected = expected_identifier
               ; actual = Option.some expression
               })
      | Option.Some
          (Operator { applicand; identifier = actual_identifier; _ }) ->
          if Qualified_identifier.equal expected_identifier actual_identifier
          then Result.ok applicand
          else
            Result.error
              (Expected_operator
                 { expected = expected_identifier
                 ; actual = Option.some applicand
                 })
      | Option.None ->
          Result.error
            (Expected_operator
               { expected = expected_identifier; actual = Option.none }))

  exception Ambiguous_operator_placement of Expression.t

  let ambiguous p =
    let* x = p in
    fail_at_previous_location (Ambiguous_operator_placement x)

  exception Missing_left_argument of Expression.t

  let missing_left_argument p =
    let* x = p in
    fail_at_previous_location (Missing_left_argument x)

  type operators =
    { prefix : Qualified_identifier.Set.t
    ; postfix : Qualified_identifier.Set.t
    ; infix_left_associative : Qualified_identifier.Set.t
    ; infix_right_associative : Qualified_identifier.Set.t
    ; infix_non_associative : Qualified_identifier.Set.t
    }

  let empty_operators =
    { prefix = Qualified_identifier.Set.empty
    ; postfix = Qualified_identifier.Set.empty
    ; infix_left_associative = Qualified_identifier.Set.empty
    ; infix_right_associative = Qualified_identifier.Set.empty
    ; infix_non_associative = Qualified_identifier.Set.empty
    }

  let add_operator identifier operator operators =
    match Operator.fixity operator with
    | Fixity.Prefix ->
        { operators with
          prefix = Qualified_identifier.Set.add identifier operators.prefix
        }
    | Fixity.Postfix ->
        { operators with
          postfix = Qualified_identifier.Set.add identifier operators.postfix
        }
    | Fixity.Infix -> (
        match Operator.associativity operator with
        | Associativity.Left_associative ->
            { operators with
              infix_left_associative =
                Qualified_identifier.Set.add identifier
                  operators.infix_left_associative
            }
        | Associativity.Right_associative ->
            { operators with
              infix_right_associative =
                Qualified_identifier.Set.add identifier
                  operators.infix_right_associative
            }
        | Associativity.Non_associative ->
            { operators with
              infix_non_associative =
                Qualified_identifier.Set.add identifier
                  operators.infix_non_associative
            })

  let group_operators primitives =
    let groups =
      List.fold_left
        (fun levels primitive ->
          match primitive with
          | Expression _ -> levels
          | Operator { identifier; operator; _ } ->
              let precedence = Operator.precedence operator in
              let level =
                Option.value ~default:empty_operators
                  (Int.Map.find_opt precedence levels)
              in
              let level' = add_operator identifier operator level in
              Int.Map.add precedence level' levels)
        Int.Map.empty primitives
    in
    List.map Pair.snd (Int.Map.bindings groups)

  (*=
    Original grammar:

    <expression> ::=
      | <prefix-op> <expression>
      | <expression> <infix-op> <expression>
      | <expression> <postfix-op>
      | <atom>+

    Rewritten grammar to handle dynamic recursive descent:

    Let M be the total number of precedence levels for the user-defined
    operators. Let R, L and N stand for right-, left- and non-associative.

    <expression m> ::= (* m <= M *)
      | <expression (m + 1)> <infix-op m N> <expression (m + 1)>
      | (<prefix-op m> | <expression (m + 1)> <infix-op m R>)+ <expression (m + 1)>
      | <expression (m + 1)> (<postfix-op m> | <infix-op m L> <expression (m + 1)>)+
      | <expression (m + 1)>

    <expression (M + 1)> ::=
      | <atom>+

    Further rewritten grammar:

    <expression m> ::= (* m <= M *)
      | <expression (m + 1)> <infix-op m N> <expression (m + 1)>
      | <expression (m + 1)> <infix-op m R> <trailing-r m>
      | <expression (m + 1)> <infix-op m L> <expression (m + 1)> <trailing-l m>
      | <expression (m + 1)> <postfix-op m> <trailing-l m>
      | <expression (m + 1)>
      | <prefix-op m> <trailing-r m>

    <trailing-r m> ::= (* Effectively (<prefix-op m> | <expression (m + 1)> <infix-op m R>)* <expression (m + 1)> *)
      | <prefix-op m> <trailing-r m>
      | <expression (m + 1)> <infix-op m R> <trailing-r m>
      | <expression (m + 1)>

    <trailing-l m> ::= (* Effectively (<postfix-op m> | <infix-op m L> <expression (m + 1)>)* *)
      | <postfix-op m> <trailing-l m>
      | <infix-op m L> <expression (m + 1)> <trailing-l m>
      | .

    <expression (M + 1)> ::=
      | <atom>+
  *)

  let operator_choice operators =
    choice (List.map operator (Qualified_identifier.Set.elements operators))

  let make_parser
      { prefix
      ; postfix
      ; infix_left_associative
      ; infix_right_associative
      ; infix_non_associative
      } fallback (* <expression (m + 1)> *) =
    let prefix_operator (* <prefix-op m> *) = operator_choice prefix
    and postfix_operator (* <postfix-op m> *) = operator_choice postfix
    and infix_left_associative_operator (* <infix-op m L> *) =
      operator_choice infix_left_associative
    and infix_right_associative_operator (* <infix-op m R> *) =
      operator_choice infix_right_associative
    and infix_non_associative_operator (* <infix-op m N> *) =
      operator_choice infix_non_associative
    in
    let ambiguous_infix_left_associative_operator =
      ambiguous infix_left_associative_operator
    and ambiguous_infix_right_associative_operator =
      ambiguous infix_right_associative_operator
    and ambiguous_infix_non_associative_operator =
      ambiguous infix_non_associative_operator
    and ambiguous_prefix_operator = ambiguous prefix_operator
    and ambiguous_postfix_operator = ambiguous postfix_operator in
    let trailing_r (* <trailing-r m> *) =
      Fun.fix (fun trailing_r ->
          choice
            [ (let* operator = prefix_operator in
               let* argument = trailing_r in
               return (prefix_application operator argument))
              (* <prefix-op m> <trailing-r m> *)
            ; (let* left_argument = fallback in
               choice
                 [ (let* operator = infix_right_associative_operator in
                    let* right_argument = trailing_r in
                    return
                      (infix_application left_argument operator
                         right_argument))
                   (* <expression (m + 1)> <infix-op m R> <trailing-r m> *)
                 ; ambiguous_infix_left_associative_operator
                 ; ambiguous_infix_non_associative_operator
                 ; ambiguous_postfix_operator
                 ; return left_argument (* <expression (m + 1)> *)
                 ])
            ; ambiguous_infix_left_associative_operator
            ; ambiguous_infix_non_associative_operator
            ; ambiguous_postfix_operator
            ])
    in
    let rec trailing_l left_argument (* <trailing-l m> *) =
      choice
        [ (let* operator = postfix_operator in
           trailing_l (postfix_application left_argument operator))
          (* <postfix-op m> <trailing-l m> *)
        ; (let* operator = infix_left_associative_operator in
           let* right_argument = fallback in
           trailing_l
             (infix_application left_argument operator right_argument))
          (* <infix-op m L> <expression (m + 1)> <trailing-l m> *)
        ; ambiguous_infix_non_associative_operator
        ; ambiguous_infix_right_associative_operator
        ; ambiguous_prefix_operator
        ; return left_argument (* . *)
        ]
    in
    choice
      [ (let* operator = prefix_operator in
         let* argument = trailing_r in
         return (prefix_application operator argument))
      ; (let* left_argument = fallback in
         choice
           [ (let* operator = postfix_operator in
              trailing_l (postfix_application left_argument operator))
           ; (let* operator = infix_left_associative_operator in
              let* right_argument = fallback in
              trailing_l
                (infix_application left_argument operator right_argument))
           ; (let* operator = infix_right_associative_operator in
              let* right_argument = trailing_r in
              return
                (infix_application left_argument operator right_argument))
           ; (let* operator = infix_non_associative_operator in
              let* right_argument = fallback in
              return
                (infix_application left_argument operator right_argument))
             <& choice
                  [ ambiguous_infix_left_associative_operator
                  ; ambiguous_infix_right_associative_operator
                  ; ambiguous_infix_non_associative_operator
                  ; return ()
                  ]
           ; return left_argument
           ])
      ; missing_left_argument
          (choice
             [ postfix_operator
             ; infix_left_associative_operator
             ; infix_right_associative_operator
             ; infix_non_associative_operator
             ])
      ]

  let juxtaposition =
    some expression >>= function
    | List1.T (expression, []) -> return (atom expression)
    | List1.T (applicand, x :: xs) ->
        let arguments = List1.map atom (List1.from x xs) in
        return (application applicand arguments)

  let rec make_parser' operators =
    match operators with
    | [] -> juxtaposition
    | o :: os -> make_parser o (make_parser' os)

  let disambiguate_application expressions =
    let expressions_list = List2.to_list expressions in
    let operator_levels = group_operators expressions_list in
    let parser = make_parser' operator_levels in
    let initial_location =
      let (List2.T (e1, _e2, _es)) = expressions in
      Location.start_position_as_location (source_location e1)
    in
    let state = initial ~initial_location (Seq.of_list expressions_list) in
    match eval (run_exn (only parser)) state with
    | Atom _expression -> assert false
    | Application { applicand; arguments; _ } -> (applicand, arguments)

  let () =
    Error.register_exception_printer (function
      | Parser_error cause ->
          let cause_printer = Error.find_printer cause in
          Format.dprintf "@[Failed to parse application.@;%t@]" cause_printer
      | Labelled_exception { label; cause } ->
          let cause_printer = Error.find_printer cause in
          Format.dprintf "%s.@;@[%t@]" label cause_printer
      | No_more_choices exceptions ->
          let exception_printers = List.map Error.find_printer exceptions in
          Format.dprintf "@[<v 2>Exhausted alternatives in parsing:@,%a@]"
            (List.pp ~pp_sep:Format.pp_print_cut
               (fun ppf exception_printer ->
                 Format.fprintf ppf "- @[%t@]" exception_printer))
            exception_printers
      | Expected_end_of_input ->
          Format.dprintf "Expected the parser input to end here."
      | Expected_expression _ ->
          Format.dprintf
            "Expected an expression, but got an operator.@ If you intended \
             to write the operator as an expression, add parentheses around \
             it."
      | Expected_operator _ ->
          Format.dprintf "Expected an operator, but got an expression."
      | Missing_left_argument _ ->
          Format.dprintf "This operator is missing its left argument."
      | Ambiguous_operator_placement _ ->
          Format.dprintf
            "This operator's placement is ambiguous.@ Add parentheses \
             around its arguments."
      | cause -> Error.raise_unsupported_exception_printing cause)
end
