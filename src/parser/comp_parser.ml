open Support
open Beluga_syntax
open Common_parser

module type COMP_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val comp_kind : Synprs.comp_sort_object t

  val comp_typ : Synprs.comp_sort_object t

  val comp_pattern : Synprs.comp_pattern_object t

  val comp_copattern : Synprs.comp_copattern_object t

  val comp_expression : Synprs.comp_expression_object t

  val comp_context : Synprs.comp_context_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t)
    (Meta_parser : Meta_parser.META_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location) :
  COMP_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location = struct
  include Parser
  include Meta_parser

  exception Ambiguous_comp_forward_arrow

  exception Ambiguous_comp_backward_arrow

  (* This recursive module is defined as a convenient alternative to
     eta-expansion or using the fixpoint combinator for defining mutually
     recursive parsers. *)
  module rec Comp_parsers : sig
    val comp_sort_object : Synprs.comp_sort_object t

    val comp_pattern_atomic_object : Synprs.comp_pattern_object t

    val comp_pattern_object : Synprs.comp_pattern_object t

    val comp_copattern_object : Synprs.comp_copattern_object t

    val comp_expression_object : Synprs.comp_expression_object t

    val comp_context : Synprs.comp_context_object t
  end = struct
    let comp_pattern_meta_context =
      many
        (braces (seq2 meta_object_identifier (maybe (colon &> meta_type))))
      |> span
      $> fun (location, bindings) ->
      { Synprs.Meta.Context_object.location; bindings }

    (*=
      Original grammar:

      <comp-sort-object> ::=
        | <identifier>
        | <qualified-identifier>
        | `ctype'
        | `{' <omittable-meta-object-identifier> [`:' <meta-thing>] `}' <comp-sort-object>
        | `(' <omittable-meta-object-identifier> [`:' <meta-thing>] `)' <comp-sort-object>
        | <comp-sort-object> <forward-arrow> <comp-sort-object>
        | <comp-sort-object> <backward-arrow> <comp-sort-object>
        | <comp-sort-object> `*' <comp-sort-object>
        | <comp-sort-object> <comp-sort-object>
        | <meta-thing>
        | `(' <comp-sort-object> `)'

      Rewritten grammar, to eliminate left-recursions, handle precedence
      using recursive descent, and handle left-associative operators.
      Weak prefix operators (Pis) may appear without parentheses
      as the rightmost operand of an operator.

      <comp-weak-prefix> ::=
        | `{' <omittable-meta-object-identifier> [`:' <meta-thing>] `}' <comp-sort-object>
        | `(' <omittable-meta-object-identifier> [`:' <meta-thing>] `)' <comp-sort-object>

      <comp-sort-object> ::=
        | <comp-sort-object1>

      <comp-sort-object1> ::=
        | <comp-weak-prefix>
        | <comp-sort-object2>

      <comp-sort-object2> ::=
        | <comp-sort-object3> (<forward-arrow> (<comp-sort-object> | <comp-weak-prefix>))+
        | <comp-sort-object3> (<backward-arrow> (<comp-sort-object> | <comp-weak-prefix>))+
        | <comp-sort-object3>

      <comp-sort-object3> ::=
        | <comp-sort-object4> (`*' <comp-sort-object>)+
        | <comp-sort-object4>

      <comp-sort-object4> ::=
        | <comp-sort-object5> (<comp-sort-object5> | <comp-weak-prefix>)+
        | <comp-sort-object5>

      <comp-sort-object5> ::=
        | <identifier>
        | <qualified-identifier>
        | `ctype'
        | <meta-thing>
        | `(' <comp-sort-object> `)'
    *)
    let comp_weak_prefix =
      let declaration =
        seq2 omittable_meta_object_identifier (maybe (colon &> meta_type))
      in
      let explicit_pi =
        seq2 (braces declaration) Comp_parsers.comp_sort_object
        |> span
        $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
             Synprs.Comp.Sort_object.Raw_pi
               { location
               ; parameter_identifier
               ; parameter_sort
               ; plicity = Plicity.explicit
               ; body
               })
        |> labelled "Explicit computational Pi kind or type"
      and implicit_pi =
        seq2 (trying (parens declaration)) Comp_parsers.comp_sort_object
        |> span
        $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
             Synprs.Comp.Sort_object.Raw_pi
               { location
               ; parameter_identifier
               ; parameter_sort
               ; plicity = Plicity.implicit
               ; body
               })
        |> labelled "Implicit computational Pi kind or type"
      in
      choice [ explicit_pi; implicit_pi ]

    let comp_sort_object5 =
      let constant_or_variable =
        qualified_or_plain_identifier |> span
        $> (function
             | location, `Qualified identifier ->
                 Synprs.Comp.Sort_object.Raw_qualified_identifier
                   { location; identifier; prefixed = false }
             | location, `Plain identifier ->
                 Synprs.Comp.Sort_object.Raw_identifier
                   { location; identifier; prefixed = false })
        |> labelled "Computational type constant or term variable"
      and ctype =
        keyword "ctype" |> span
        $> (fun (location, ()) ->
             Synprs.Comp.Sort_object.Raw_ctype { location })
        |> labelled "Computational `ctype' kind"
      and meta_object_or_meta_type =
        (* Needs [trying] because meta-types can be parenthesized, and the
           leading `(' is ambiguous with [parenthesized]. *)
        trying (alt meta_object meta_type)
        |> span
        $> (fun (location, boxed) ->
             Synprs.Comp.Sort_object.Raw_box { location; boxed })
        |> labelled "Computational boxed meta-object or meta-type"
      and parenthesized =
        parens Comp_parsers.comp_sort_object
        |> span
        $> (function
             | location, Synprs.Comp.Sort_object.Raw_identifier i ->
                 Synprs.Comp.Sort_object.Raw_identifier
                   { i with prefixed = true; location }
             | location, Synprs.Comp.Sort_object.Raw_qualified_identifier i
               ->
                 Synprs.Comp.Sort_object.Raw_qualified_identifier
                   { i with prefixed = true; location }
             | location, sort ->
                 Synprs.set_location_of_comp_sort_object location sort)
        |> labelled "Parenthesized computational kind or type"
      in
      choice
        [ constant_or_variable
        ; ctype
        ; meta_object_or_meta_type
        ; parenthesized
        ]

    let comp_sort_object4 =
      seq2 comp_sort_object5 (many (alt comp_sort_object5 comp_weak_prefix))
      |> span
      $> function
      | _, (object_, []) -> object_
      | location, (o1, o2 :: os) ->
          let objects = List2.from o1 o2 os in
          Synprs.Comp.Sort_object.Raw_application { location; objects }

    let comp_sort_object3 =
      seq2 comp_sort_object4 (many (star &> comp_sort_object4)) |> span
      $> function
      | _, (object_, []) -> object_
      | location, (o1, o2 :: os) ->
          let operands = List2.from o1 o2 os in
          Synprs.Comp.Sort_object.Raw_cross { location; operands }

    let comp_sort_object2 =
      (* Forward arrows are right-associative, and backward arrows are
         left-associative. Forward and backward arrows have the same
         precedence. Mixing forward and backward arrows at the same
         precedence level is ambiguous. That is, [a -> b <- c] could be
         parsed as [a -> (b <- c)] when parsed from left to right, or as [(a
         -> b) <- c] when parsed from right to left. *)
      let forward_arrow_operator = forward_arrow $> fun () -> `Forward_arrow
      and backward_arrow_operator =
        backward_arrow $> fun () -> `Backward_arrow
      and right_operand = alt comp_sort_object3 comp_weak_prefix in
      comp_sort_object3 >>= fun object_ ->
      (maybe (alt forward_arrow_operator backward_arrow_operator)
       >>= function
       | Option.None -> return (`Singleton object_)
       | Option.Some `Forward_arrow ->
           (* A forward arrow was parsed. Subsequent backward arrows are
              ambiguous. *)
           let backward_arrow =
             backward_arrow >>= fun () ->
             fail_at_previous_location Ambiguous_comp_backward_arrow
           and forward_arrow = forward_arrow_operator in
           let operator = alt backward_arrow forward_arrow in
           seq2 right_operand (many (operator &> right_operand))
           $> fun (x, xs) -> `Forward_arrows (List1.from object_ (x :: xs))
       | Option.Some `Backward_arrow ->
           (* A backward arrow was parsed. Subsequent forward arrows are
              ambiguous. *)
           let backward_arrow_operator = backward_arrow
           and forward_arrow_operator =
             forward_arrow >>= fun () ->
             fail_at_previous_location Ambiguous_comp_forward_arrow
           in
           let operator =
             alt forward_arrow_operator backward_arrow_operator
           in
           seq2 right_operand (many (operator &> right_operand))
           $> fun (x, xs) -> `Backward_arrows (List1.from object_ (x :: xs)))
      $> function
      | `Singleton x -> x
      | `Forward_arrows xs ->
          List1.fold_right Fun.id
            (fun operand accumulator ->
              let location =
                Location.join
                  (Synprs.location_of_comp_sort_object operand)
                  (Synprs.location_of_comp_sort_object accumulator)
              in
              Synprs.Comp.Sort_object.Raw_arrow
                { location
                ; domain = operand
                ; range = accumulator
                ; orientation = `Forward
                })
            xs
      | `Backward_arrows (List1.T (x, xs)) ->
          List.fold_left
            (fun accumulator operand ->
              let location =
                Location.join
                  (Synprs.location_of_comp_sort_object accumulator)
                  (Synprs.location_of_comp_sort_object operand)
              in
              Synprs.Comp.Sort_object.Raw_arrow
                { location
                ; domain = operand
                ; range = accumulator
                ; orientation = `Backward
                })
            x xs

    let comp_sort_object1 = choice [ comp_weak_prefix; comp_sort_object2 ]

    let comp_sort_object =
      comp_sort_object1 |> labelled "Computation-level type or kind"

    (*=
      Original grammar:

      <comp-pattern-atomic-object> ::=
        | <identifier>
        | <qualified-identifier>
        | <boxed-meta-object-thing>
        | <dot-qualified-identifier> <comp-pattern-atomic-object>*
        | `_'
        | `(' <comp-pattern-object> (`,' <comp-pattern-object>)+ `)'
        | `(' <comp-pattern-object> `)'

      <comp-pattern-object> ::=
        | <identifier>
        | <qualified-identifier>
        | <boxed-meta-object-thing>
        | `(' <comp-pattern-object> (`,' <comp-pattern-object>)+ `)'
        | <comp-pattern-object> <comp-pattern-object>
        | <dot-qualified-identifier> <comp-pattern-object>*
        | <comp-pattern-object> `:' <comp-type>
        | `{' <omittable-meta-object-identifier> `:' <meta-thing> `}' <comp-pattern-object>
        | `_'
        | `(' <comp-pattern-object> `)'

      Rewritten grammar, to eliminate left-recursions, handle precedence
      using recursive descent, and handle left-associative operators.
      Weak prefix operators (Pis) may appear without parentheses
      as the rightmost operand of an operator.

      <comp-weak-prefix-pattern> ::=
        | `{' <omittable-meta-object-identifier> `:' <meta-thing> `}' <comp-pattern-object>

      <comp-pattern-object> ::=
        | <comp-pattern-object1>

      <comp-pattern-object1> ::=
        | <comp-weak-prefix-pattern>
        | <comp-pattern-object2>

      <comp-pattern-object2> ::=
        | <comp-pattern-object3> (`:' <comp-type>)+
        | <comp-pattern-object3>

      <comp-pattern-object3> ::=
        | <comp-pattern-object4> (<comp-pattern-object4> | <comp-weak-prefix-pattern>)+
        | <comp-pattern-object4>

      <comp-pattern-object4> ::=
        | <identifier>
        | <qualified-identifier>
        | <boxed-meta-object-thing>
        | `_'
        | `(' <comp-pattern-object> (`,' <comp-pattern-object>)+ `)'
        | `(' <comp-pattern-object> `)'

      <comp-atomic-pattern-object> ::=
        | <comp-pattern-object4>

      <comp-copattern-object> ::=
        | <dot-qualified-identifier>
        | <comp-pattern-object4>
      *)
    let comp_weak_prefix_pattern =
      let pi =
        seq2
          (braces
             (seq2 omittable_meta_object_identifier
                (maybe (colon &> meta_type))))
          Comp_parsers.comp_pattern_object
        |> span
        $> (fun (location, ((parameter_identifier, parameter_typ), pattern)) ->
             Synprs.Comp.Pattern_object.Raw_meta_annotated
               { location; parameter_identifier; parameter_typ; pattern })
        |> labelled "Meta-annotated computation-level pattern"
      in
      pi

    let comp_pattern_object4 =
      let constant_or_variable =
        qualified_or_plain_identifier |> span
        $> (function
             | location, `Qualified identifier ->
                 Synprs.Comp.Pattern_object.Raw_qualified_identifier
                   { location; identifier; prefixed = false }
             | location, `Plain identifier ->
                 Synprs.Comp.Pattern_object.Raw_identifier
                   { location; identifier; prefixed = false })
        |> labelled "Computational type constant or term variable"
      and box =
        meta_pattern |> span
        $> (fun (location, pattern) ->
             Synprs.Comp.Pattern_object.Raw_box { location; pattern })
        |> labelled "Meta-object pattern"
      and wildcard =
        underscore |> span
        $> (fun (location, ()) ->
             Synprs.Comp.Pattern_object.Raw_wildcard { location })
        |> labelled "Computational wildcard pattern"
      and parenthesized_or_tuple =
        parens (sep_by1 ~sep:comma Comp_parsers.comp_pattern_object)
        |> span
        $> (function
             | ( location
               , List1.T (Synprs.Comp.Pattern_object.Raw_identifier i, []) )
               ->
                 Synprs.Comp.Pattern_object.Raw_identifier
                   { i with prefixed = true; location }
             | ( location
               , List1.T
                   (Synprs.Comp.Pattern_object.Raw_qualified_identifier i, [])
               ) ->
                 Synprs.Comp.Pattern_object.Raw_qualified_identifier
                   { i with prefixed = true; location }
             | location, List1.T (pattern, []) ->
                 Synprs.set_location_of_comp_pattern_object location pattern
             | location, List1.T (p1, p2 :: ps) ->
                 let elements = List2.from p1 p2 ps in
                 Synprs.Comp.Pattern_object.Raw_tuple { location; elements })
        |> labelled "Computational tuple pattern or parenthesized pattern"
      in
      choice [ constant_or_variable; box; wildcard; parenthesized_or_tuple ]

    let comp_pattern_object3 =
      seq2 comp_pattern_object4
        (many (alt comp_pattern_object4 comp_weak_prefix_pattern))
      |> span
      $> function
      | _, (pattern, []) -> pattern
      | location, (p1, p2 :: ps) ->
          let patterns = List2.from p1 p2 ps in
          Synprs.Comp.Pattern_object.Raw_application { location; patterns }

    let comp_pattern_object2 =
      let annotation = colon &> comp_sort_object in
      let trailing_annotations = many (span annotation) in
      seq2 comp_pattern_object3 trailing_annotations $> function
      | pattern, [] -> pattern
      | pattern, annotations ->
          List.fold_left
            (fun accumulator (sort_location, typ) ->
              let location =
                Location.join
                  (Synprs.location_of_comp_pattern_object accumulator)
                  sort_location
              in
              Synprs.Comp.Pattern_object.Raw_annotated
                { location; pattern = accumulator; typ })
            pattern annotations

    let comp_pattern_object1 =
      choice [ comp_weak_prefix_pattern; comp_pattern_object2 ]

    let comp_pattern_object =
      comp_pattern_object1 |> labelled "Computation-level pattern"

    let comp_pattern_atomic_object =
      comp_pattern_object4 |> labelled "Computation-level atomic pattern"

    let comp_copattern_object =
      let observation =
        dot &> qualified_identifier |> span
        $> (fun (location, observation) ->
             Synprs.Comp.Copattern_object.Raw_observation
               { location; observation })
        |> labelled "Computation-level destructor pattern"
      and pattern =
        Comp_parsers.comp_pattern_atomic_object |> span
        $> (fun (location, pattern) ->
             Synprs.Comp.Copattern_object.Raw_pattern { location; pattern })
        |> labelled "Computation-level application copattern"
      in
      choice [ observation; pattern ]
      |> labelled "Computation-level copattern"

    (*=
      Original grammar:

      <comp-expression-object> ::=
        | <identifier>
        | <qualified-identifier>
        | `fn' <omittable-identifier>+ <thick-forward-arrow> <comp-expression>
        | `fun' [`|'] <comp-pattern-atomic-object>+ <thick-forward-arrow> <comp-expression-object>
          (`|' <comp-pattern-atomic-object>+ <thick-forward-arrow> <comp-expression-object>)*
        | `mlam' <omittable-meta-object-identifier>+ <thick-forward-arrow> <comp-expression-object>
        | `let' <comp-pattern-object> `=' <comp-expression-object> `in' <comp-expression-object>
        | <boxed-meta-object-thing>
        | `impossible' <comp-expression-object>
        | `case' <comp-expression-object> [`--not'] `of'
          [`|'] <comp-pattern-object> <thick-forward-arrow> <comp-expression-object>
          (`|' <comp-pattern-object> <thick-forward-arrow> <comp-expression-object>)*
        | `(' <comp-expression-object> (`,' <comp-expression-object>)+ `)'
        | `?' [<identifier>]
        | `_'
        | <comp-expression-object> <comp-expression-object>
        | <comp-expression-object> <dot-qualified-identifier>
        | <qualified-identifier> <comp-expression-object>*
        | <comp-expression-object> `:' <comp-type>
        | `(' <comp-expression-object> `)'

      Rewritten grammar, to eliminate left-recursions, handle precedence
      using recursive descent, and handle left-associative operators.

      <comp-expression-object> ::=
        | <comp-expression-object1>

      <comp-expression-object1> ::=
        | <comp-expression-object2> (`:' <comp-sort-object>)+
        | <comp-expression-object2>

      <comp-expression-object2> ::=
        | <comp-expression-object3> <comp-expression-object3>+
        | <comp-expression-object3>

      <comp-expression-object3> ::=
        | `fn' <omittable-identifier>+ <thick-forward-arrow> <comp-expression>
        | `fun' [`|'] <comp-pattern-atomic-object>+ <thick-forward-arrow> <comp-expression-object>
          (`|' <comp-pattern-atomic-object>+ <thick-forward-arrow> <comp-expression-object>)*
        | `mlam' <omittable-meta-object-identifier>+ <thick-forward-arrow> <comp-expression-object>
        | `let' <comp-pattern-object> `=' <comp-expression-object> `in' <comp-expression-object>
        | `impossible' <comp-expression-object>
        | `case' <comp-expression-object> [`--not'] `of'
          [`|'] <comp-pattern-object> <thick-forward-arrow> <comp-expression-object>
          (`|' <comp-pattern-object> <thick-forward-arrow> <comp-expression-object>)*
        | <comp-expresion-object4>

      <comp-expresion-object4> ::=
        | <comp-expresion-object5> <dot-qualified-identifier>+
        | <comp-expresion-object5>

      <comp-expresion-object5> ::=
        | <identifier>
        | <qualified-identifier>
        | <boxed-meta-object-thing>
        | `?' [<identifier>]
        | `_'
        | `(' <comp-expression-object> (`,' <comp-expression-object>)+ `)'
        | `(' <comp-expression-object> `)'
      *)
    let comp_expression_object5 =
      let constant_or_variable =
        qualified_or_plain_identifier |> span
        $> (function
             | location, `Qualified identifier ->
                 Synprs.Comp.Expression_object.Raw_qualified_identifier
                   { location; identifier; prefixed = false }
             | location, `Plain identifier ->
                 Synprs.Comp.Expression_object.Raw_identifier
                   { location; identifier; prefixed = false })
        |> labelled "Computational type constant or term variable"
      and box =
        meta_object |> span
        $> (fun (location, meta_object) ->
             Synprs.Comp.Expression_object.Raw_box { location; meta_object })
        |> labelled "Boxed meta-object"
      and hole =
        hole |> span
        $> (function
             | location, `Unlabelled ->
                 let label = Option.none in
                 Synprs.Comp.Expression_object.Raw_hole { location; label }
             | location, `Labelled label ->
                 let label = Option.some label in
                 Synprs.Comp.Expression_object.Raw_hole { location; label })
        |> labelled "Computational hole"
      and box_hole =
        underscore |> span
        $> (fun (location, ()) ->
             Synprs.Comp.Expression_object.Raw_box_hole { location })
        |> labelled "Box hole"
      and parenthesized_or_tuple =
        parens (sep_by1 ~sep:comma Comp_parsers.comp_expression_object)
        |> span
        $> (function
             | ( location
               , List1.T (Synprs.Comp.Expression_object.Raw_identifier i, [])
               ) ->
                 Synprs.Comp.Expression_object.Raw_identifier
                   { i with prefixed = true; location }
             | ( location
               , List1.T
                   ( Synprs.Comp.Expression_object.Raw_qualified_identifier i
                   , [] ) ) ->
                 Synprs.Comp.Expression_object.Raw_qualified_identifier
                   { i with prefixed = true; location }
             | location, List1.T (expression, []) ->
                 Synprs.set_location_of_comp_expression_object location
                   expression
             | location, List1.T (e1, e2 :: es) ->
                 let elements = List2.from e1 e2 es in
                 Synprs.Comp.Expression_object.Raw_tuple
                   { location; elements })
        |> labelled "Computational tuple or parenthesized expression"
      in
      choice
        [ constant_or_variable; box; hole; box_hole; parenthesized_or_tuple ]

    let comp_expression_object4 =
      seq2 comp_expression_object5
        (maybe
           (dot &> qualified_identifier)
           (* Repeated dot qualified identifiers are impossible by the
              lexical convention. *))
      |> span
      $> (function
           | _location, (expression, Option.None) -> expression
           | location, (scrutinee, Option.Some destructor) ->
               Synprs.Comp.Expression_object.Raw_observation
                 { location; scrutinee; destructor })
      |> labelled "Computational atomic or observation expression"

    let comp_expression_object3 =
      let comma_opt =
        (*= Optionally parse a comma, for backwards compatibility with
          `fn x1, x2, ..., xn => e' and `mlam X1, X2, ..., Xn => e'. *)
        void (maybe comma)
      in
      let fn =
        seq2
          (keyword "fn" &> sep_by1 ~sep:comma_opt omittable_identifier)
          (thick_forward_arrow &> Comp_parsers.comp_expression_object)
        |> span
        $> (fun (location, (parameters, body)) ->
             Synprs.Comp.Expression_object.Raw_fn
               { location; parameters; body })
        |> labelled "Ordinary function abstraction"
      and cofunction =
        keyword "fun" &> maybe pipe
        &> sep_by1 ~sep:pipe
             (seq3 comp_pattern_meta_context
                (sep_by1 ~sep:comma_opt comp_copattern_object)
                (thick_forward_arrow &> Comp_parsers.comp_expression_object))
        |> span
        $> (fun (location, branches) ->
             Synprs.Comp.Expression_object.Raw_fun { location; branches })
        |> labelled "Pattern-matching function abstraction"
      and mlam =
        seq2
          (keyword "mlam" &> some omittable_meta_object_identifier)
          (thick_forward_arrow &> Comp_parsers.comp_expression_object)
        |> span
        $> (fun (location, (parameters, body)) ->
             Synprs.Comp.Expression_object.Raw_mlam
               { location; parameters; body })
        |> labelled "Meta-level function abstraction"
      and let_ =
        seq4
          (keyword "let" &> comp_pattern_meta_context)
          Comp_parsers.comp_pattern_object
          (equals &> Comp_parsers.comp_expression_object)
          (keyword "in" &> Comp_parsers.comp_expression_object)
        |> span
        $> (fun (location, (meta_context, pattern, scrutinee, body)) ->
             Synprs.Comp.Expression_object.Raw_let
               { location; meta_context; pattern; scrutinee; body })
        |> labelled "`let'-expressions"
      and impossible =
        keyword "impossible" &> Comp_parsers.comp_expression_object |> span
        $> (fun (location, scrutinee) ->
             Synprs.Comp.Expression_object.Raw_impossible
               { location; scrutinee })
        |> labelled "Empty `impossible' case analysis"
      and case =
        seq3
          (keyword "case" &> Comp_parsers.comp_expression_object)
          (keyword "of" &> maybe (pragma "not"))
          (maybe pipe
          &> sep_by1 ~sep:pipe
               (seq3 comp_pattern_meta_context
                  Comp_parsers.comp_pattern_object
                  (thick_forward_arrow &> Comp_parsers.comp_expression_object))
          )
        |> span
        $> (fun (location, (scrutinee, check_coverage, branches)) ->
             let check_coverage = Option.is_none check_coverage in
             Synprs.Comp.Expression_object.Raw_case
               { location; scrutinee; check_coverage; branches })
        |> labelled "Pattern-matching expression"
      in
      choice
        [ fn
        ; cofunction
        ; mlam
        ; let_
        ; impossible
        ; case
        ; comp_expression_object4
        ]

    let comp_expression_object2 =
      some comp_expression_object3 |> span $> function
      | _, List1.T (expression, []) -> expression
      | location, List1.T (x1, x2 :: xs) ->
          let expressions = List2.from x1 x2 xs in
          Synprs.Comp.Expression_object.Raw_application
            { location; expressions }

    let comp_expression_object1 =
      let annotation = colon &> comp_sort_object in
      let trailing_annotations = many (span annotation) in
      seq2 comp_expression_object2 trailing_annotations $> function
      | expression, [] -> expression
      | expression, annotations ->
          List.fold_left
            (fun accumulator (sort_location, typ) ->
              let location =
                Location.join
                  (Synprs.location_of_comp_expression_object accumulator)
                  sort_location
              in
              Synprs.Comp.Expression_object.Raw_annotated
                { location; expression = accumulator; typ })
            expression annotations

    let comp_expression_object =
      comp_expression_object1 |> labelled "Computation-level expression"

    (*=
      <comp-context> ::=
        | [`^']
        | <identifier> [`:' <comp-type>] (`,' <identifier> [`:' <comp-type>])*
      *)
    let comp_context =
      let non_empty =
        sep_by0 ~sep:comma
          (seq2 identifier (maybe (colon &> Comp_parsers.comp_sort_object)))
        |> span
        $> fun (location, bindings) ->
        { Synprs.Comp.Context_object.location; bindings }
      and empty =
        maybe hat |> span $> fun (location, _) ->
        { Synprs.Comp.Context_object.location; bindings = [] }
      in
      choice [ non_empty; empty ]
  end

  let comp_sort_object = Comp_parsers.comp_sort_object

  let comp_pattern =
    Comp_parsers.comp_pattern_object |> labelled "Computation-level pattern"

  let comp_copattern =
    Comp_parsers.comp_copattern_object
    |> labelled "Computation-level copattern"

  let comp_expression =
    Comp_parsers.comp_expression_object
    |> labelled "Computation-level expression"

  let comp_context =
    Comp_parsers.comp_context |> labelled "Computation-level context"

  let comp_kind = comp_sort_object |> labelled "Computation-level kind"

  let comp_typ = comp_sort_object |> labelled "Computation-level type"

  let () =
    Error.register_exception_printer (function
      | Ambiguous_comp_forward_arrow ->
          Format.dprintf
            "This computation-level forward arrow operator is ambiguous."
      | Ambiguous_comp_backward_arrow ->
          Format.dprintf
            "This computation-level backward arrow operator is ambiguous."
      | cause -> Error.raise_unsupported_exception_printing cause)
end
