open Support
open Beluga_syntax
open Common_parser

exception Ambiguous_clf_forward_arrow

exception Ambiguous_clf_backward_arrow

module rec CLF_parsers : sig
  val clf_object : Synprs.CLF.Object.t t

  val clf_context_object : Synprs.CLF.Context_object.t t
end = struct
  (*=
      Original grammar:

      <clf-context-object> ::=
        | [`^']
        | `..'
        | [`..' `,'] [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*

      <clf-object> ::=
        | `{' <omittable-identifier> `:' <clf-object> `}' <clf-object>
        | `\' <omittable-identifier> [`:' <clf-object>] `.' <clf-object>
        | <clf-object> <forward-arrow> <clf-object>
        | <clf-object> <backward-arrow> <clf-object>
        | <clf-object> `:' <clf-object>
        | `block' `(' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>)+ `)'
        | `block' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>)+
        | `block' `(' <clf-object> `)'
        | `block' <clf-object>
        | <clf-object> <clf-object>
        | <clf-object> `[' <clf-context-object> `]'
        | <clf-object>`.'<identifier>
        | <clf-object>`.'<integer>
        | `_'
        | `?'[<identifier>]
        | <identifier>
        | <qualified-identifier>
        | `<' <clf-object> (`;' <clf-object>)* `>'
        | `(' <clf-object> `)'


      Rewritten grammar, to eliminate left-recursions, handle precedence
      using recursive descent, and handle left-associative operators.
      Weak prefix operators (lambdas and Pis) may appear without parentheses
      as the rightmost operand of an operator.

      <clf-context-object> ::=
        | [`^']
        | `..'
        | [`..' `,'] [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*

      <clf-weak-prefix> ::=
        | `{' <omittable-identifier> [`:' <lf-object>] `}' <lf-object>
        | `\' <omittable-identifier> [`:' <lf-object>] `.' <lf-object>

      <clf-object> ::=
        | <clf-object1>

      <clf-object1> ::=
        | <clf-weak-prefix>
        | <clf-object2>

      <clf-object2> ::=
        | <clf-object3> (`:' (<clf-object3> | <clf-weak-prefix>))+
        | <clf-object3>

      <clf-object3> ::=
        | <clf-object4> (<forward-arrow> (<clf-object4> | <clf-weak-prefix>))+
        | <clf-object4> (<backward-arrow> (<clf-object4> | <clf-weak-prefix>))+
        | <clf-object4>

      <clf-object4> ::=
        | `block' `(' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>)+ `)'
        | `block' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>)+
        | `block' `(' <clf-object> `)'
        | `block' <clf-object>
        | <clf-object5>

      <clf-object5> ::=
        | <clf-object6> (<clf-object6> | <clf-weak-prefix>)+
        | <clf-object6>

      <clf-object6> ::=
        | <clf-object7> (`[' <clf-context-object> `]')+
        | <clf-object7>

      <clf-object7> ::=
        | <clf-object8>(`.'(<integer> | <identifier>))+
        | <clf-object8>

      <clf-object8> ::=
        | <identifier>
        | <qualified-identifier>
        | `_'
        | `?'[<identifier>]
        | `<' <clf-object> (`;' <clf-object>)* `>'
        | `(' <clf-object> `)'
  *)
  let clf_weak_prefix =
    let lambda =
      seq2
        (lambda
        &> seq2 omittable_identifier
             (maybe (colon &> CLF_parsers.clf_object))
        <& dot)
        CLF_parsers.clf_object
      |> span
      $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
           Synprs.CLF.Object.Raw_lambda
             { location; parameter_identifier; parameter_sort; body })
      |> labelled "Contextual LF lambda term"
    and pi =
      seq2
        (braces
           (seq2 omittable_identifier
              (maybe (colon &> CLF_parsers.clf_object))))
        CLF_parsers.clf_object
      |> span
      $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
           Synprs.CLF.Object.Raw_pi
             { location; parameter_identifier; parameter_sort; body })
      |> labelled "Contextual LF Pi kind or type"
    in
    choice [ lambda; pi ]

  let clf_context_object =
    let empty =
      maybe hat |> span $> fun (location, _) ->
      { Synprs.CLF.Context_object.location
      ; head = Synprs.CLF.Context_object.Head.None { location }
      ; objects = []
      }
    and identity =
      dots |> span $> fun (location, ()) ->
      { Synprs.CLF.Context_object.location
      ; head = Synprs.CLF.Context_object.Head.Identity { location }
      ; objects = []
      }
    and non_empty =
      let bindings =
        sep_by1
          (seq2 (maybe (identifier <& trying colon)) CLF_parsers.clf_object)
          comma
      in
      seq2 (maybe (seq2 (span dots) (trying comma))) bindings |> span
      $> function
      | location, (Option.Some ((dots_location, ()), ()), objects) ->
          { Synprs.CLF.Context_object.location
          ; head =
              Synprs.CLF.Context_object.Head.Identity
                { location = dots_location }
          ; objects = List1.to_list objects
          }
      | location, (Option.None, objects) ->
          { Synprs.CLF.Context_object.location
          ; head =
              Synprs.CLF.Context_object.Head.None
                { location = Location.start_position_as_location location }
          ; objects = List1.to_list objects
          }
    in
    choice [ non_empty; identity; empty ]
    |> labelled "Contextual LF substitution or context object"

  let clf_object8 =
    let constant_or_variable =
      qualified_or_plain_identifier |> span
      $> (function
           | location, `Qualified identifier ->
               Synprs.CLF.Object.Raw_qualified_identifier
                 { location; identifier; quoted = false }
           | location, `Plain identifier ->
               Synprs.CLF.Object.Raw_identifier
                 { location
                 ; identifier = (identifier, `Plain)
                 ; quoted = false
                 })
      |> labelled "Contextual LF constant or variable"
    and parameter_variable =
      hash_identifier $> fun identifier ->
      let location = Identifier.location identifier in
      Synprs.CLF.Object.Raw_identifier
        { location; identifier = (identifier, `Hash); quoted = false }
    and substitution_variable =
      dollar_identifier $> fun identifier ->
      let location = Identifier.location identifier in
      Synprs.CLF.Object.Raw_identifier
        { location; identifier = (identifier, `Dollar); quoted = false }
    and underscore_hole =
      underscore |> span
      $> (fun (location, ()) ->
           Synprs.CLF.Object.Raw_hole { location; variant = `Underscore })
      |> labelled "Contextual LF hole"
    and possibly_labelled_hole =
      hole |> span
      $> (fun (location, variant) ->
           Synprs.CLF.Object.Raw_hole { location; variant })
      |> labelled "Possibly labelled contextual LF hole"
    and tuple =
      angles (sep_by1 CLF_parsers.clf_object semicolon)
      |> span
      $> (fun (location, elements) ->
           Synprs.CLF.Object.Raw_tuple { location; elements })
      |> labelled "Contextual LF tuple term"
    and parenthesized_or_quoted_constant_or_variable =
      parens CLF_parsers.clf_object
      |> span
      $> (function
           | location, Synprs.CLF.Object.Raw_identifier i ->
               Synprs.CLF.Object.Raw_identifier
                 { i with quoted = true; location }
           | location, Synprs.CLF.Object.Raw_qualified_identifier i ->
               Synprs.CLF.Object.Raw_qualified_identifier
                 { i with quoted = true; location }
           | location, o -> Synprs.set_location_of_clf_object location o)
      |> labelled "Contextual LF parenthesized kind, type or term"
    in
    choice
      [ constant_or_variable
      ; parameter_variable
      ; substitution_variable
      ; underscore_hole
      ; possibly_labelled_hole
      ; tuple
      ; parenthesized_or_quoted_constant_or_variable
      ]

  let clf_object7 =
    (* Projections are left-associative. *)
    let integer_projection = dot_integer $> fun i -> `By_position i
    and identifier_projection =
      dot_identifier $> fun x -> `By_identifier x
    in
    let projection = alt integer_projection identifier_projection in
    let trailing_projections = many (span projection) in
    (* If a term only uses named projections, then those projections are
       actually parsed as a qualfified identifier. *)
    seq2 clf_object8 trailing_projections
    $> (function
         | object_, [] -> object_
         | object_, projections ->
             List.fold_left
               (fun accumulator (projection_location, projection) ->
                 let location =
                   Location.join
                     (Synprs.location_of_clf_object accumulator)
                     projection_location
                 in
                 Synprs.CLF.Object.Raw_projection
                   { location; object_ = accumulator; projection })
               object_ projections)
    |> labelled "Contextual LF atomic object or projection term"

  let clf_object6 =
    (* Substitutions are left-associative. *)
    seq2 clf_object7 (many (span (bracks clf_context_object)))
    $> (function
         | object_, [] -> object_
         | object_, substitutions ->
             List.fold_left
               (fun accumulator (substitution_location, substitution) ->
                 let location =
                   Location.join
                     (Synprs.location_of_clf_object accumulator)
                     substitution_location
                 in
                 Synprs.CLF.Object.Raw_substitution
                   { location; object_ = accumulator; substitution })
               object_ substitutions)
    |> labelled
         "Contextual LF atomic object, projection term orsubstitution term"

  let clf_object5 =
    seq2 clf_object6 (many (alt clf_object6 clf_weak_prefix))
    |> span
    $> (function
         | _, (object_, []) -> object_
         | location, (o1, o2 :: os) ->
             Synprs.CLF.Object.Raw_application
               { location; objects = List2.from o1 o2 os })
    |> labelled
         "Contextual LF atomic object, projection term, substitution term \
          or application"

  let clf_object4 =
    let block_contents =
      sep_by1
        (seq2 (maybe (identifier <& trying colon)) CLF_parsers.clf_object)
        comma
    in
    let block =
      keyword "block" &> opt_parens block_contents |> span
      $> (fun (location, elements) ->
           Synprs.CLF.Object.Raw_block { location; elements })
      |> labelled "Contextual LF block type"
    in
    choice [ block; clf_object5 ]

  let clf_object3 =
    (* Forward arrows are right-associative, and backward arrows are
       left-associative. Forward and backward arrows have the same
       precedence. Mixing forward and backward arrows at the same precedence
       level is ambiguous. That is, [a -> b <- c] could be parsed as [a -> (b
       <- c)] when parsed from left to right, or as [(a -> b) <- c] when
       parsed from right to left. *)
    let forward_arrow_operator = forward_arrow $> fun () -> `Forward_arrow
    and backward_arrow_operator = backward_arrow $> fun () -> `Backward_arrow
    and right_operand = alt clf_object4 clf_weak_prefix in
    clf_object4 >>= fun object_ ->
    maybe (alt forward_arrow_operator backward_arrow_operator)
    >>= (function
          | Option.None -> return (`Singleton object_)
          | Option.Some `Forward_arrow ->
              (* A forward arrow was parsed. Subsequent backward arrows are
                 ambiguous. *)
              let backward_arrow =
                backward_arrow >>= fun () ->
                fail Ambiguous_clf_backward_arrow
              and forward_arrow = forward_arrow_operator in
              let operator = alt backward_arrow forward_arrow in
              seq2 right_operand (many (operator &> right_operand))
              $> fun (x, xs) ->
              `Forward_arrows (List1.from object_ (x :: xs))
          | Option.Some `Backward_arrow ->
              (* A backward arrow was parsed. Subsequent forward arrows are
                 ambiguous. *)
              let backward_arrow_operator = backward_arrow
              and forward_arrow_operator =
                forward_arrow >>= fun () -> fail Ambiguous_clf_forward_arrow
              in
              let operator =
                alt forward_arrow_operator backward_arrow_operator
              in
              seq2 right_operand (many (operator &> right_operand))
              $> fun (x, xs) ->
              `Backward_arrows (List1.from object_ (x :: xs)))
    $> (function
         | `Singleton x -> x
         | `Forward_arrows xs ->
             List1.fold_right Fun.id
               (fun operand accumulator ->
                 let location =
                   Location.join
                     (Synprs.location_of_clf_object operand)
                     (Synprs.location_of_clf_object accumulator)
                 in
                 Synprs.CLF.Object.Raw_arrow
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
                     (Synprs.location_of_clf_object accumulator)
                     (Synprs.location_of_clf_object operand)
                 in
                 Synprs.CLF.Object.Raw_arrow
                   { location
                   ; domain = operand
                   ; range = accumulator
                   ; orientation = `Backward
                   })
               x xs)
    |> labelled
         "Contextual LF atomic object, application, annotated term, forward \
          arrow or backward arrow"

  let clf_object2 =
    let annotation = colon &> alt clf_object3 clf_weak_prefix in
    let trailing_annotations = many (span annotation) in
    seq2 clf_object3 trailing_annotations
    $> (function
         | object_, [] -> object_
         | object_, annotations ->
             List.fold_left
               (fun accumulator (sort_location, sort) ->
                 let location =
                   Location.join
                     (Synprs.location_of_clf_object accumulator)
                     sort_location
                 in
                 Synprs.CLF.Object.Raw_annotated
                   { location; object_ = accumulator; sort })
               object_ annotations)
    |> labelled
         "Contextual LF atomic object, application, annotatedterm, \
          forwardarrow or backward arrow object"

  let clf_object1 = choice [ clf_weak_prefix; clf_object2 ]

  let clf_object = clf_object1 |> labelled "Contextual LF object"
end

let clf_object = CLF_parsers.clf_object

let clf_context_object = CLF_parsers.clf_context_object
