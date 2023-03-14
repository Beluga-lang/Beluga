open Support
open Beluga_syntax
open Common_parser

module type META_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val schema : Synprs.schema_object t

  val meta_type : Synprs.meta_thing t

  val meta_object : Synprs.meta_thing t

  val meta_pattern : Synprs.meta_thing t

  val meta_context : Synprs.meta_context_object t
end

module Make
    (Parser : COMMON_PARSER
                with type token = Location.t * Token.t
                 and type location = Location.t)
    (Lf_parser : Lf_parser.LF_PARSER
                   with type token = Parser.token
                    and type input = Parser.input
                    and type state = Parser.state
                    and type location = Parser.location)
    (Clf_parser : Clf_parser.CLF_PARSER
                    with type token = Parser.token
                     and type input = Parser.input
                     and type state = Parser.state
                     and type location = Parser.location) :
  META_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location = struct
  include Parser
  include Lf_parser
  include Clf_parser

  (* This recursive module is defined as a convenient alternative to
     eta-expansion or using the fixpoint combinator for defining mutually
     recursive parsers. *)
  module rec Meta_parsers : sig
    val schema_object : Synprs.schema_object t

    val meta_type : Synprs.meta_thing t

    val meta_object : Synprs.meta_thing t

    val meta_context : Synprs.meta_context_object t
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
        | <qualified-identifier>
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
        | <qualified-identifier>
        | `(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `#(' <clf-context-object> <turnstile> <clf-context-object> `)'
        | `$(' <clf-context-object> (<turnstile> | <turnstile-hash>) <clf-context-object> `)'
        | `[' <clf-context-object> [<turnstile> <clf-context-object>] `]'
        | `#[' <clf-context-object> <turnstile> <clf-context-object> `]'
        | `$[' <clf-context-object> (<turnstile> | <turnstile-hash>) <clf-context-object> `]'
    *)
    let schema_some_clause =
      let declaration = seq2 identifier (colon &> lf_typ) in
      keyword "some"
      &> bracks (sep_by1 ~sep:comma declaration)
      |> labelled "Context schema `some' clause"

    let schema_block_clause =
      let block_contents =
        sep_by1 ~sep:comma (seq2 (maybe (identifier <& trying colon)) lf_typ)
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
        seq2 schema_some_clause schema_block_clause
        |> span
        $> (fun (location, (some_clause, block_clause)) ->
             Synprs.Meta.Schema_object.Raw_element
               { location
               ; some = Option.some some_clause
               ; block = block_clause
               })
        |> labelled "`some'-`block' schema"
      and element =
        schema_block_clause |> span
        $> (fun (location, block_clause) ->
             Synprs.Meta.Schema_object.Raw_element
               { location; some = Option.none; block = block_clause })
        |> labelled "`block' schema"
      in
      choice [ constant; element_with_some; element ]

    let schema_object1 =
      sep_by1 ~sep:plus schema_object2 |> span $> function
      | _, List1.T (schema_object, []) -> schema_object
      | location, List1.T (c1, c2 :: cs) ->
          let schemas = List2.from c1 c2 cs in
          Synprs.Meta.Schema_object.Raw_alternation { location; schemas }

    let schema_object = schema_object1 |> labelled "Context schema"

    let meta_type =
      let schema_type =
        qualified_identifier |> span
        $> (fun (location, schema) ->
             Synprs.Meta.Thing.RawSchema { location; schema })
        |> labelled "Schema meta-type"
      and plain_inner_thing = seq2 clf_context (turnstile &> clf_context)
      and hash_inner_thing = seq2 clf_context (turnstile &> clf_context)
      and dollar_inner_thing =
        let turnstile = turnstile $> fun () -> `Plain
        and turnstile_hash = turnstile_hash $> fun () -> `Hash in
        seq2 clf_context
          (seq2 (alt turnstile turnstile_hash) clf_substitution)
      in
      let plain_meta_type =
        choice
          [ parens plain_inner_thing
            |> labelled "Plain meta-type in parentheses"
          ; bracks plain_inner_thing
            |> labelled "Plain meta-type in brackets"
          ]
        |> span
        $> fun (location, (context, object_)) ->
        Synprs.Meta.Thing.RawTurnstile
          { location; context; object_; variant = `Plain }
      and hash_meta_type =
        choice
          [ hash_parens hash_inner_thing
            |> labelled "Parameter type in parentheses"
          ; hash_bracks hash_inner_thing
            |> labelled "Parameter type in brackets"
          ]
        |> span
        $> fun (location, (context, object_)) ->
        Synprs.Meta.Thing.RawTurnstile
          { location; context; object_; variant = `Hash }
      and dollar_meta_type =
        choice
          [ dollar_parens dollar_inner_thing
            |> labelled "Substitution type in parentheses"
          ; dollar_bracks dollar_inner_thing
            |> labelled "Substitution type in brackets"
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
      choice
        [ schema_type; plain_meta_type; hash_meta_type; dollar_meta_type ]
      |> labelled "Meta-type"

    let meta_object =
      let plain_inner_thing =
        seq2 clf_context (maybe (turnstile &> clf_context))
      and dollar_inner_thing =
        let turnstile = turnstile $> fun () -> `Plain
        and turnstile_hash = turnstile_hash $> fun () -> `Hash in
        seq2 clf_context
          (seq2 (alt turnstile turnstile_hash) clf_substitution)
      in
      let plain_meta_object =
        bracks plain_inner_thing
        |> labelled "Contextual term or context"
        |> span
        $> function
        | location, (context, Option.None) ->
            Synprs.Meta.Thing.RawContext { location; context }
        | location, (context, Option.Some object_) ->
            Synprs.Meta.Thing.RawTurnstile
              { location; context; object_; variant = `Plain }
      and dollar_meta_object =
        dollar_bracks dollar_inner_thing
        |> labelled "Substitution object"
        |> span
        $> function
        | location, (context, (`Plain, object_)) ->
            Synprs.Meta.Thing.RawTurnstile
              { location; context; object_; variant = `Dollar }
        | location, (context, (`Hash, object_)) ->
            Synprs.Meta.Thing.RawTurnstile
              { location; context; object_; variant = `Dollar_hash }
      in
      choice [ plain_meta_object; dollar_meta_object ]
      |> labelled "Meta-object"

    (*=
      <meta-context> ::=
        | [`^']
        | <meta-object-identifier> [`:' <boxed-meta-type>] (`,' <meta-object-identifier> [`:' <boxed-meta-type>])*
    *)
    let meta_context =
      let non_empty =
        sep_by0 ~sep:comma
          (seq2 meta_object_identifier
             (maybe (colon &> Meta_parsers.meta_type)))
        |> span
        $> fun (location, bindings) ->
        { Synprs.Meta.Context_object.location; bindings }
      and empty =
        maybe hat |> span $> fun (location, _) ->
        { Synprs.Meta.Context_object.location; bindings = [] }
      in
      choice [ non_empty; empty ]
  end

  let schema = Meta_parsers.schema_object |> labelled "Schema"

  let meta_type = Meta_parsers.meta_type |> labelled "Meta-type"

  let meta_object = Meta_parsers.meta_object |> labelled "Meta-object"

  let meta_pattern =
    Meta_parsers.meta_object |> labelled "Meta-object pattern"

  let meta_context =
    Meta_parsers.meta_context |> labelled "Meta-level context"
end
