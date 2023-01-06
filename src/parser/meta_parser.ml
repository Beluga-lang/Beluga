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
    &> bracks (sep_by1 declaration comma)
    |> labelled "Context schema `some' clause"

  let schema_block_clause =
    let block_contents =
      sep_by1
        (seq2 (maybe (identifier <& trying colon)) Clf_parser.clf_object)
        comma
      |> labelled "Context schema element"
    in
    keyword "block" &> opt_parens block_contents
    |> labelled "Context schema `block' clause"

  let schema_object2 =
    let constant =
      qualified_identifier $> fun identifier ->
      let location = Qualified_identifier.location identifier in
      Synprs.Meta.Schema_object.Raw_constant { location; identifier }
    and element =
      seq2 (maybe schema_some_clause) schema_block_clause
      |> span
      $> (fun (location, (some_clause, block_clause)) ->
           Synprs.Meta.Schema_object.Raw_element
             { location; some = some_clause; block = block_clause })
      |> labelled "Context schema atom"
    in
    choice [ constant; element ]

  let schema_object1 =
    sep_by1 schema_object2 plus
    |> span
    $> (function
         | _, List1.T (schema_object, []) -> schema_object
         | location, List1.T (c1, c2 :: cs) ->
             let schemas = List2.from c1 c2 cs in
             Synprs.Meta.Schema_object.Raw_alternation { location; schemas })
    |> labelled "Context schema constant, atom or alternation"

  let schema_object = schema_object1

  let meta_thing =
    let schema_type =
      schema_object |> span $> fun (location, schema) ->
      Synprs.Meta.Thing.RawSchema { location; schema }
    and meta_type_or_meta_object =
      let plain_inner_thing =
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
        choice [ parens plain_inner_thing; bracks plain_inner_thing ] |> span
        $> function
        | location, (context, Option.None) ->
            Synprs.Meta.Thing.RawContext { location; context }
        | location, (context, Option.Some object_) ->
            Synprs.Meta.Thing.RawTurnstile
              { location; context; object_; variant = `Plain }
      and hash_meta_type =
        choice [ hash_parens hash_inner_thing; hash_bracks hash_inner_thing ]
        |> span
        $> fun (location, (context, object_)) ->
        Synprs.Meta.Thing.RawTurnstile
          { location; context; object_; variant = `Hash }
      and dollar_meta_type =
        choice
          [ dollar_parens dollar_inner_thing
          ; dollar_bracks dollar_inner_thing
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
      choice [ plain_meta_type; hash_meta_type; dollar_meta_type ]
    in
    choice [ schema_type; meta_type_or_meta_object ]
    |> labelled "Meta-type, meta-object, or meta-object pattern"

  (*=
      <meta-context> ::=
        | [`^']
        | <meta-object-identifier> [`:' <boxed-meta-type>] (`,' <meta-object-identifier> [`:' <boxed-meta-type>])*
  *)
  let meta_context =
    let non_empty =
      sep_by0
        (seq2 meta_object_identifier
           (maybe (colon &> Meta_parsers.meta_thing)))
        comma
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
