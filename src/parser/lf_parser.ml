open Support
open Beluga_syntax
open Common_parser

module type LF_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val lf_kind : Synprs.lf_object t

  val lf_typ : Synprs.lf_object t

  val lf_term : Synprs.lf_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t) :
  LF_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location = struct
  include Parser

  exception Ambiguous_lf_forward_arrow

  exception Ambiguous_lf_backward_arrow

  (* This recursive module is defined as a convenient alternative to
     eta-expansion or using the fixpoint combinator for defining mutually
     recursive parsers. *)
  module rec LF_parsers : sig
    val lf_object : Synprs.lf_object t
  end = struct
    (*=
      Original grammar:

      <lf-object> ::=
        | `{' <omittable-identifier> [`:' <lf-object>] `}' <lf-object>
        | `\' <omittable-identifier> [`:' <lf-object>] `.' <lf-object>
        | <lf-object> <forward-arrow> <lf-object>
        | <lf-object> <backward-arrow> <lf-object>
        | <lf-object> `:' <lf-object>
        | <lf-object> <lf-object>
        | <identifier>
        | <qualified-identifier>
        | `type'
        | `_'
        | `(' <lf-object> `)'


      Rewritten grammar, to eliminate left-recursions, handle precedence
      using recursive descent, and handle left-associative operators.
      Weak prefix operators (lambdas and Pis) may appear without parentheses
      as the rightmost operand of an operator.

      <lf-weak-prefix> ::=
        | `{' <omittable-identifier> [`:' <lf-object>] `}' <lf-object>
        | `\' <omittable-identifier> [`:' <lf-object>] `.' <lf-object>

      <lf-object> ::=
        | <lf-object1>

      <lf-object1> ::=
        | <lf-weak-prefix>
        | <lf-object2>

      <lf-object2> ::=
        | <lf-object3> (`:' (<lf-object3> | <lf-weak-prefix>))+
        | <lf-object3>

      <lf-object3> ::=
        | <lf-object4> (<forward-arrow> (<lf-object4> | <lf-weak-prefix>))+
        | <lf-object4> (<backward-arrow> (<lf-object4> | <lf-weak-prefix>))+
        | <lf-object4>

      <lf-object4> ::=
        | <lf-object5> (<lf-object5> | <lf-weak-prefix>)+
        | <lf-object5>

      <lf-object5> ::=
        | <identifier>
        | <qualified-identifier>
        | `type'
        | `_'
        | `(' <lf-object> `)'
    *)
    let lf_weak_prefix =
      let declaration =
        seq2 omittable_identifier (maybe (colon &> LF_parsers.lf_object))
      in
      let lambda =
        seq2
          (lambda
          &> seq2 omittable_identifier
               (maybe (colon &> LF_parsers.lf_object))
          <& dot)
          LF_parsers.lf_object
        |> span
        $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
             Synprs.LF.Object.Raw_lambda
               { location; parameter_identifier; parameter_sort; body })
        |> labelled "LF lambda term"
      and explicit_pi =
        seq2 (braces declaration) LF_parsers.lf_object
        |> span
        $> (fun (location, ((parameter_identifier, parameter_sort), body)) ->
             Synprs.LF.Object.Raw_pi
               { location
               ; parameter_identifier
               ; parameter_sort
               ; plicity = Plicity.explicit
               ; body
               })
        |> labelled "LF explicit dependent product type or kind"
      in
      (* There is no syntax for implict Pis *)
      choice [ lambda; explicit_pi ]

    let lf_object5 =
      let constant_or_variable =
        qualified_or_plain_identifier |> span
        $> (function
             | location, `Qualified identifier ->
                 Synprs.LF.Object.Raw_qualified_identifier
                   { location; identifier; prefixed = false }
             | location, `Plain identifier ->
                 Synprs.LF.Object.Raw_identifier
                   { location; identifier; prefixed = false })
        |> labelled
             "LF term-level constant, type-level constant, or variable"
      and type_ =
        keyword "type" |> span
        $> (fun (location, ()) -> Synprs.LF.Object.Raw_type { location })
        |> labelled "LF `type' kind"
      and hole =
        underscore |> span
        $> (fun (location, ()) -> Synprs.LF.Object.Raw_hole { location })
        |> labelled "LF wildcard"
      and parenthesized_or_prefixed_constant_or_variable =
        parens LF_parsers.lf_object
        |> span
        $> (function
             | location, Synprs.LF.Object.Raw_identifier i ->
                 Synprs.LF.Object.Raw_identifier
                   { i with prefixed = true; location }
             | location, Synprs.LF.Object.Raw_qualified_identifier i ->
                 Synprs.LF.Object.Raw_qualified_identifier
                   { i with prefixed = true; location }
             | location, o -> Synprs.set_location_of_lf_object location o)
        |> labelled
             "LF parenthesized kind, type or term, or a prefixed constant"
      in
      choice
        [ constant_or_variable
        ; type_
        ; hole
        ; parenthesized_or_prefixed_constant_or_variable
        ]

    let lf_object4 =
      seq2 lf_object5 (many (alt lf_object5 lf_weak_prefix)) |> span
      $> function
      | _, (object_, []) -> object_
      | location, (o1, o2 :: os) ->
          Synprs.LF.Object.Raw_application
            { location; objects = List2.from o1 o2 os }

    let lf_object3 =
      (* Forward arrows are right-associative, and backward arrows are
         left-associative. Forward and backward arrows have the same
         precedence. Mixing forward and backward arrows at the same
         precedence level is ambiguous. That is, [a -> b <- c] could be
         parsed as [a -> (b <- c)] when parsed from left to right, or as [(a
         -> b) <- c] when parsed from right to left. *)
      let forward_arrow_operator = forward_arrow $> fun () -> `Forward_arrow
      and backward_arrow_operator =
        backward_arrow $> fun () -> `Backward_arrow
      and right_operand = alt lf_object4 lf_weak_prefix in
      lf_object4 >>= fun object_ ->
      (maybe (alt forward_arrow_operator backward_arrow_operator)
       >>= function
       | Option.None -> return (`Singleton object_)
       | Option.Some `Forward_arrow ->
           (* A forward arrow was parsed. Subsequent backward arrows are
              ambiguous. *)
           let backward_arrow =
             backward_arrow >>= fun () ->
             fail_at_previous_location Ambiguous_lf_backward_arrow
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
             fail_at_previous_location Ambiguous_lf_forward_arrow
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
                  (Synprs.location_of_lf_object operand)
                  (Synprs.location_of_lf_object accumulator)
              in
              Synprs.LF.Object.Raw_arrow
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
                  (Synprs.location_of_lf_object accumulator)
                  (Synprs.location_of_lf_object operand)
              in
              Synprs.LF.Object.Raw_arrow
                { location
                ; domain = operand
                ; range = accumulator
                ; orientation = `Backward
                })
            x xs

    let lf_object2 =
      (* Annotations are left-associative. *)
      let annotation = colon &> alt lf_object3 lf_weak_prefix in
      let trailing_annotations = many (span annotation) in
      seq2 lf_object3 trailing_annotations $> function
      | object_, [] -> object_
      | object_, annotations ->
          List.fold_left
            (fun accumulator (sort_location, sort) ->
              let location =
                Location.join
                  (Synprs.location_of_lf_object accumulator)
                  sort_location
              in
              Synprs.LF.Object.Raw_annotated
                { location; object_ = accumulator; sort })
            object_ annotations

    let lf_object1 = choice [ lf_weak_prefix; lf_object2 ]

    let lf_object = lf_object1 |> labelled "LF kind, type or term"
  end

  let lf_object = LF_parsers.lf_object

  let lf_kind = lf_object |> labelled "LF kind"

  let lf_typ = lf_object |> labelled "LF type"

  let lf_term = lf_object |> labelled "LF term"

  let () =
    Error.register_exception_printer (function
      | Ambiguous_lf_forward_arrow ->
          Format.dprintf "This LF forward arrow operator is ambiguous."
      | Ambiguous_lf_backward_arrow ->
          Format.dprintf "This LF backward arrow operator is ambiguous."
      | exn -> Error.raise_unsupported_exception_printing exn)
end
