open Support
open Beluga_syntax
open Common_parser

module rec Meta_parsers : sig
  val schema_object : Synprs.Meta.Schema_object.t t

  val meta_thing : Synprs.Meta.Thing.t t

  val meta_context : Synprs.Meta.Context_object.t t
end = struct
  (*=
      Original grammar:

      <schema-object> ::=
        | <qualified-identifier>
        | <schema-object> `+' <schema-object>
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*

      <meta-thing> ::=
        | <schema-object>
        | `(' <clf-context-object> `)'
        | `(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `#(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `$(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `$(' <clf-context-object> <turnstile-hash> <clf-context-object> `)'
        | `[' <clf-context-object> `]'
        | `[' <clf-context-object> <turnstile> <clf-context-object> `]'
        | `#[' <clf-context-object> <turnstile> <clf-context-object> `]'
        | `$[' <clf-context-object> <turnstile> <clf-context-object> `]'
        | `$[' <clf-context-object> <turnstile-hash> <clf-context-object> `]'

      Rewritten grammar, to eliminate left-recursions, and handle precedence
      using recursive descent.

      <schema-object> ::=
        | <schema-object1>

      <schema-object1> ::=
        | <schema-object2> (`+' <schema-object2>)+
        | <schema-object2>

      <schema-object2> ::=
        | <qualified-identifier>
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*

      <meta-thing> ::=
        | <schema-object>
        | `(' <clf-context-object> [<turnstile> <clf-context-object>] `)'
        | `#(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `$(' <clf-context-object> (<turnstile> | <turnstile-hash>) <clf-context-object> `)'
        | `[' <clf-context-object> [<turnstile> <clf-context-object>] `]'
        | `#[' <clf-context-object> <turnstile> <clf-context-object> `]'
        | `$[' <clf-context-object> (<turnstile> | <turnstile-hash>) <clf-context-object> `]'
  *)
  let schema_some_clause =
    let declaration = seq2 identifier (colon &> Clf_parser.clf_object) in
    keyword "some"
    &> bracks (sep_by1 ~sep:comma declaration)
    |> labelled "Context schema `some' clause"

  let schema_block_clause =
    let block_contents =
      sep_by1 ~sep:comma
        (seq2 (maybe (identifier <& trying colon)) Clf_parser.clf_object)
      |> labelled "Context schema element"
    in
    keyword "block" &> opt_parens block_contents
    |> labelled "Context schema `block' clause"

  let schema_object2 =
    let constant =
      qualified_identifier
      $> (fun identifier ->
           let location = Qualified_identifier.location identifier in
           Synprs.Meta.Schema_object.Raw_constant { location; identifier })
      |> labelled "Schema constant"
    and element_with_some =
      seq2 schema_some_clause schema_block_clause |> span
      $> fun (location, (some_clause, block_clause)) ->
      Synprs.Meta.Schema_object.Raw_element
        { location; some = Option.some some_clause; block = block_clause }
    and element =
      schema_block_clause |> span $> fun (location, block_clause) ->
      Synprs.Meta.Schema_object.Raw_element
        { location; some = Option.none; block = block_clause }
    in
    choice [ constant; element_with_some; element ]

  let schema_object1 =
    sep_by1 ~sep:plus schema_object2 |> span $> function
    | _, List1.T (schema_object, []) -> schema_object
    | location, List1.T (c1, c2 :: cs) ->
        let schemas = List2.from c1 c2 cs in
        Synprs.Meta.Schema_object.Raw_alternation { location; schemas }

  let schema_object = schema_object1 |> labelled "Context schema"

  let meta_thing =
    let schema_type =
      schema_object |> span
      $> (fun (location, schema) ->
           Synprs.Meta.Thing.RawSchema { location; schema })
      |> labelled "Schema meta-type"
    and plain_inner_thing =
      seq2 Clf_parser.clf_context_object
        (maybe (turnstile &> Clf_parser.clf_context_object))
    and hash_inner_thing =
      seq2 Clf_parser.clf_context_object
        (turnstile &> Clf_parser.clf_context_object)
    and dollar_inner_thing =
      let turnstile = turnstile $> fun () -> `Plain
      and turnstile_hash = turnstile_hash $> fun () -> `Hash in
      seq2 Clf_parser.clf_context_object
        (seq2 (alt turnstile turnstile_hash) Clf_parser.clf_context_object)
    in
    let plain_meta_type =
      choice
        [ parens plain_inner_thing
          |> labelled "Plain meta-type or object in parentheses"
        ; bracks plain_inner_thing
          |> labelled "Plain meta-type or object in brackets"
        ]
      |> span
      $> function
      | location, (context, Option.None) ->
          Synprs.Meta.Thing.RawContext { location; context }
      | location, (context, Option.Some object_) ->
          Synprs.Meta.Thing.RawTurnstile
            { location; context; object_; variant = `Plain }
    and hash_meta_type =
      choice
        [ hash_parens hash_inner_thing
          |> labelled "Parameter type or term in parentheses"
        ; hash_bracks hash_inner_thing
          |> labelled "Parameter type or term in brackets"
        ]
      |> span
      $> fun (location, (context, object_)) ->
      Synprs.Meta.Thing.RawTurnstile
        { location; context; object_; variant = `Hash }
    and dollar_meta_type =
      choice
        [ dollar_parens dollar_inner_thing
          |> labelled "Substitution type or object in parentheses"
        ; dollar_bracks dollar_inner_thing
          |> labelled "Substitution type or object in brackets"
        ]
      |> span
      $> function
      | location, (context, (`Plain, object_)) ->
          Synprs.Meta.Thing.RawTurnstile
            { location; context; object_; variant = `Dollar }
      | location, (context, (`Hash, object_)) ->
          Synprs.Meta.Thing.RawTurnstile
            { location; context; object_; variant = `Dollar_hash }
    in
    choice [ schema_type; plain_meta_type; hash_meta_type; dollar_meta_type ]
    |> labelled "Meta-type or object"

  (*=
      <meta-context> ::=
        | [`^']
        | <meta-object-identifier> [`:' <boxed-meta-type>] (`,' <meta-object-identifier> [`:' <boxed-meta-type>])*
  *)
  let meta_context =
    let non_empty =
      sep_by0 ~sep:comma
        (seq2 meta_object_identifier
           (maybe (colon &> Meta_parsers.meta_thing)))
      |> span
      $> fun (location, bindings) ->
      { Synprs.Meta.Context_object.location; bindings }
    and empty =
      maybe hat |> span $> fun (location, _) ->
      { Synprs.Meta.Context_object.location; bindings = [] }
    in
    choice [ non_empty; empty ]
end

let schema_object = Meta_parsers.schema_object

let meta_thing = Meta_parsers.meta_thing

let meta_context = Meta_parsers.meta_context
