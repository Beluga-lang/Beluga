open Support
open Beluga_syntax
open Common_parser

module type SIGNATURE_PARSER = sig
  (** @closed *)
  include COMMON_PARSER

  val signature : Synprs.signature t

  val signature_global_pragma : Synprs.signature_global_pragma t

  val signature_entry : Synprs.signature_entry t

  val signature_declaration : Synprs.signature_declaration t

  val trust_totality_declaration : Synprs.signature_totality_declaration t

  val named_totality_declaration : Synprs.signature_totality_declaration t

  val numeric_totality_declaration : Synprs.signature_totality_declaration t

  val totality_declaration : Synprs.signature_totality_declaration t
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
                     and type location = Parser.location)
    (Meta_parser : Meta_parser.META_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location)
    (Comp_parser : Comp_parser.COMP_PARSER
                     with type token = Parser.token
                      and type input = Parser.input
                      and type state = Parser.state
                      and type location = Parser.location)
    (Harpoon_parser : Harpoon_parser.HARPOON_PARSER
                        with type token = Parser.token
                         and type input = Parser.input
                         and type state = Parser.state
                         and type location = Parser.location) :
  SIGNATURE_PARSER
    with type token = Parser.token
     and type input = Parser.input
     and type state = Parser.state
     and type location = Parser.location = struct
  include Parser
  include Lf_parser
  include Clf_parser
  include Meta_parser
  include Comp_parser
  include Harpoon_parser

  (* This recursive module is defined as a convenient alternative to
     eta-expansion or using the fixpoint combinator for defining mutually
     recursive parsers. *)
  module rec Schema_parsers : sig
    (** [schema_object] is a schema at the signature-level.

        This version of the parser for schema objects supports schemas like:

        - [some \[\]]
        - [some \[\] block exp t]
        - [exp t] *)
    val schema_object : Synprs.schema_object t
  end = struct
    (*=
      Original grammar:

      <schema-object> ::=
        | <qualified-identifier>
        | <schema-object> `+' <schema-object>
        | [`some' `[' `]']
          [`block'] `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          [`block'] `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' `]']
          [`block'] [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          [`block'] [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*

      Rewritten grammar, to eliminate left-recursions, and handle precedence
      using recursive descent.

      <schema-object> ::=
        | <schema-object1>

      <schema-object1> ::=
        | <schema-object2> (`+' <schema-object2>)+
        | <schema-object2>

      <schema-object2> ::=
        | <qualified-identifier>
        | [`some' `[' `]']
          `block' `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' `(' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)* `)'
        | [`some' `[' `]']
          `block' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*
        | [`some' `[' <identifier> `:' <clf-object> (`,' <identifier> `:' <clf-object>) `]']
          `block' [<identifier> `:'] <clf-object> (`,' [<identifier> `:'] <clf-object>)*
    *)
    let schema_some_clause =
      let declaration = seq2 identifier (colon &> lf_typ) in
      keyword "some"
      &> bracks (sep_by0 ~sep:comma declaration)
      |> labelled "Context schema `some' clause"

    let schema_block_clause =
      let block_contents =
        sep_by1 ~sep:comma (seq2 (maybe (identifier <& trying colon)) lf_typ)
        |> labelled "Context schema element"
      in
      maybe (keyword "block")
      &> opt_parens block_contents
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
        $> (function
             | location, ([], block_clause) ->
                 Synprs.Meta.Schema_object.Raw_element
                   { location; some = Option.none; block = block_clause }
             | location, (x :: xs, block_clause) ->
                 Synprs.Meta.Schema_object.Raw_element
                   { location
                   ; some = Option.some (List1.from x xs)
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
      choice [ element_with_some; element; constant ]

    let schema_object1 =
      sep_by1 ~sep:plus schema_object2 |> span $> function
      | _, List1.T (schema_object, []) -> schema_object
      | location, List1.T (c1, c2 :: cs) ->
          let schemas = List2.from c1 c2 cs in
          Synprs.Meta.Schema_object.Raw_alternation { location; schemas }

    let schema_object = schema_object1 |> labelled "Context schema"
  end

  let schema = Schema_parsers.schema_object |> labelled "Schema"

  (* This recursive module is defined as a convenient alternative to
     eta-expansion or using the fixpoint combinator for defining mutually
     recursive parsers. *)
  module rec Signature_parsers : sig
    val signature : Synprs.signature t

    val signature_global_pragma : Synprs.signature_global_pragma t

    val signature_entry : Synprs.signature_entry t

    val signature_declaration : Synprs.signature_declaration t

    val trust_totality_declaration : Synprs.signature_totality_declaration t

    val named_totality_declaration : Synprs.signature_totality_declaration t

    val numeric_totality_declaration :
      Synprs.signature_totality_declaration t

    val totality_declaration : Synprs.signature_totality_declaration t
  end = struct
    let nostrenghten_pragma =
      pragma "nostrengthen" |> span $> fun (location, ()) ->
      Synprs.Signature.Global_pragma.No_strengthening { location }

    let coverage_pragma =
      pragma "coverage" |> span $> fun (location, ()) ->
      Synprs.Signature.Global_pragma.Raise_error_on_coverage_error
        { location }

    let warncoverage_pragma =
      pragma "warncoverage" |> span $> fun (location, ()) ->
      Synprs.Signature.Global_pragma.Warn_on_coverage_error { location }

    let signature_global_pragma =
      choice [ nostrenghten_pragma; coverage_pragma; warncoverage_pragma ]
      |> labelled "global pragma"

    let name_pragma =
      seq3
        (pragma "name" &> qualified_identifier)
        identifier
        (maybe identifier <& dot)
      |> labelled "name pragma" |> span
      $> fun ( location
             , (constant, meta_variable_base, computation_variable_base) ) ->
      Synprs.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }

    let signature_lf_const_decl =
      seq2 (identifier <& colon) lf_typ
      |> span
      $> (fun (location, (identifier, typ)) ->
           Synprs.Signature.Declaration.Raw_lf_term_constant
             { location; identifier; typ })
      |> labelled "LF term-level constant declaration"

    let signature_lf_typ_decl =
      let lf_typ_decl_body =
        let typ_decl = seq2 (identifier <& colon) lf_kind in
        seq2 (typ_decl <& equals)
          (maybe pipe &> sep_by0 ~sep:pipe signature_lf_const_decl)
        |> span
        $> fun (location, ((identifier, kind), constructor_declarations)) ->
        let typ_declaration =
          Synprs.Signature.Declaration.Raw_lf_typ_constant
            { location; identifier; kind }
        in
        List1.from typ_declaration constructor_declarations
      in
      keyword "LF"
      &> sep_by1
           ~sep:(keyword "and" &> maybe (keyword "LF") |> void)
           lf_typ_decl_body
      <& semicolon |> span
      $> (fun (location, declarations) ->
           let declarations' = List1.flatten declarations in
           Synprs.Signature.Declaration.Raw_recursive_declarations
             { location; declarations = declarations' })
      |> labelled "LF type declaration block"

    let named_totality_argument =
      identifier |> span $> fun (location, argument) ->
      Synprs.Signature.Totality.Order.Argument { location; argument }

    let numeric_totality_argument =
      integer |> span $> fun (location, argument) ->
      Synprs.Signature.Totality.Order.Argument { location; argument }

    let total_order totality_argument =
      let argument = totality_argument
      and lexical_ordering =
        braces (some totality_argument) |> span
        $> fun (location, arguments) ->
        Synprs.Signature.Totality.Order.Lexical_ordering
          { location; arguments }
      and simultaneous_ordering =
        bracks (some totality_argument) |> span
        $> fun (location, arguments) ->
        Synprs.Signature.Totality.Order.Simultaneous_ordering
          { location; arguments }
      in
      choice [ argument; lexical_ordering; simultaneous_ordering ]
      |> labelled "totality ordering"

    let trust_totality_declaration =
      keyword "trust" |> span
      $> (fun (location, ()) ->
           Synprs.Signature.Totality.Declaration.Trust { location })
      |> labelled "trust totality"

    let named_totality_declaration =
      seq2
        (trying (maybe (total_order named_totality_argument)))
        (parens (seq2 identifier (many omittable_identifier)))
      |> span
      $> fun (location, (order, (program, argument_labels))) ->
      Synprs.Signature.Totality.Declaration.Named
        { location; order; program; argument_labels }

    let numeric_totality_declaration =
      maybe (total_order numeric_totality_argument) |> span
      $> fun (location, order) ->
      Synprs.Signature.Totality.Declaration.Numeric { location; order }

    let totality_declaration =
      let total =
        keyword "total"
        &> alt named_totality_declaration numeric_totality_declaration
      in
      alt trust_totality_declaration total |> labelled "totality declaration"

    (** Mutual block of computation type declarations. *)
    let signature_cmp_typ_decl =
      let cmp_typ_decl =
        let inductive = keyword "inductive" $> fun () -> `Inductive
        and stratified = keyword "stratified" $> fun () -> `Stratified in
        let flavour = choice [ inductive; stratified ] in
        let signature_cmp_typ_decl_body =
          seq2 (identifier <& colon) comp_typ |> span
          $> fun (location, (identifier, typ)) ->
          Synprs.Signature.Declaration.Raw_comp_expression_constructor
            { location; identifier; typ }
        in
        seq4 flavour (identifier <& colon)
          (comp_kind <& equals <& maybe pipe)
          (sep_by0 ~sep:pipe signature_cmp_typ_decl_body)
        |> span
        $> fun ( location
               , ( datatype_flavour
                 , identifier
                 , kind
                 , constructor_declarations ) ) ->
        let typ_declaration =
          match datatype_flavour with
          | `Inductive ->
              Synprs.Signature.Declaration.Raw_inductive_comp_typ_constant
                { location; identifier; kind }
          | `Stratified ->
              Synprs.Signature.Declaration.Raw_stratified_comp_typ_constant
                { location; identifier; kind }
        in
        List1.from typ_declaration constructor_declarations
      in
      let cmp_cotyp_decl =
        let cmp_cotyp_body =
          seq2
            (opt_parens (seq2 (identifier <& colon) comp_typ) <& double_colon)
            comp_typ
          |> span
          $> fun (location, ((identifier, observation_type), return_type)) ->
          Synprs.Signature.Declaration.Raw_comp_expression_destructor
            { location; identifier; observation_type; return_type }
        in
        seq3
          (keyword "coinductive" &> identifier <& colon)
          (comp_kind <& equals <& maybe pipe)
          (sep_by0 ~sep:pipe cmp_cotyp_body)
        |> span
        $> fun (location, (identifier, kind, destructor_declarations)) ->
        let cotyp_declaration =
          Synprs.Signature.Declaration.Raw_comp_cotyp_constant
            { location; identifier; kind }
        in
        List1.from cotyp_declaration destructor_declarations
      in
      sep_by1 ~sep:(keyword "and") (alt cmp_typ_decl cmp_cotyp_decl)
      <& semicolon |> span
      $> (fun (location, declarations) ->
           let declarations' = List1.flatten declarations in
           Synprs.Signature.Declaration.Raw_recursive_declarations
             { location; declarations = declarations' })
      |> labelled
           "Inductive, stratified or coinductive computation type \
            declaration"

    let query_pragma =
      let bound =
        alt (star $> fun () -> Option.none) (integer $> Option.some)
        |> labelled "search bound"
      and meta_context =
        many
          (braces (seq2 meta_object_identifier (maybe (colon &> meta_type))))
        |> span
        $> fun (location, bindings) ->
        { Synprs.Meta.Context_object.location; bindings }
      in
      pragma "query"
      &> seq4 (seq2 bound bound) meta_context
           (maybe (identifier <& colon))
           lf_typ
      <& dot |> span
      |> labelled "logic programming engine query pragma"
      $> fun ( location
             , ( (expected_solutions, maximum_tries)
               , meta_context
               , identifier
               , typ ) ) ->
      Synprs.Signature.Pragma.Raw_query
        { location
        ; identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        }

    let signature_oldstyle_lf_decl =
      seq2 (identifier <& colon) (alt lf_kind lf_typ)
      <& dot |> span
      $> (fun (location, (identifier, typ_or_const)) ->
           Synprs.Signature.Declaration.Raw_lf_typ_or_term_constant
             { location; identifier; typ_or_const })
      |> labelled "old-style LF type or term constant declaration"

    let not_pragma =
      pragma "not" |> span $> fun (location, ()) ->
      Synprs.Signature.Pragma.Not { location }

    let left_associativity =
      keyword "left"
      $> Fun.const Associativity.left_associative
      |> labelled "associativity `left'"

    let right_associativity =
      keyword "right"
      $> Fun.const Associativity.right_associative
      |> labelled "associativity `right'"

    let non_associativity =
      keyword "none"
      $> Fun.const Associativity.non_associative
      |> labelled "associativity `none'"

    let associativity =
      choice [ left_associativity; right_associativity; non_associativity ]
      |> labelled "associativity"

    let prefix_pragma =
      pragma "prefix"
      &> seq2 qualified_identifier (maybe integer)
      <& dot |> span
      $> fun (location, (constant, precedence)) ->
      Synprs.Signature.Pragma.Prefix_fixity
        { location; constant; precedence }

    let infix_pragma =
      pragma "infix"
      &> seq3 qualified_identifier (maybe integer) (maybe associativity)
      <& dot |> span
      $> fun (location, (constant, precedence, associativity)) ->
      Synprs.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity }

    let postfix_pragma =
      pragma "postfix"
      &> seq2 qualified_identifier (maybe integer)
      <& dot |> span
      $> fun (location, (constant, precedence)) ->
      Synprs.Signature.Pragma.Postfix_fixity
        { location; constant; precedence }

    let fixity_pragma =
      choice [ prefix_pragma; infix_pragma; postfix_pragma ]

    let default_associativity_pragma =
      pragma "assoc" &> associativity <& dot |> span
      $> fun (location, associativity) ->
      Synprs.Signature.Pragma.Default_associativity
        { location; associativity }

    let open_pragma =
      pragma "open" &> qualified_identifier <& dot |> span
      $> (fun (location, module_identifier) ->
           Synprs.Signature.Pragma.Open_module
             { location; module_identifier })
      |> labelled "open module pragma"

    let abbrev_pragma =
      pragma "abbrev"
      &> seq2 qualified_identifier identifier
      <& dot |> span
      $> (fun (location, (module_identifier, abbreviation)) ->
           Synprs.Signature.Pragma.Abbreviation
             { location; module_identifier; abbreviation })
      |> labelled "module abbreviation pragma"

    let signature_typedef_decl =
      seq3
        (keyword "typedef" &> identifier)
        (colon &> comp_kind)
        (equals &> comp_typ <& semicolon)
      |> span
      |> labelled "type synonym declaration"
      $> fun (location, (identifier, kind, typ)) ->
      Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
        { location; identifier; kind; typ }

    let signature_schema_decl =
      seq2 (keyword "schema" &> identifier <& equals) schema
      <& semicolon |> span
      $> (fun (location, (identifier, schema)) ->
           Synprs.Signature.Declaration.Raw_schema
             { location; identifier; schema })
      |> labelled "Context schema declaration"

    let signature_let_decl =
      seq2
        (keyword "let" &> seq2 identifier (maybe (colon &> comp_typ)))
        (equals &> comp_expression <& semicolon)
      |> span
      |> labelled "value declaration"
      $> fun (location, ((identifier, typ), expression)) ->
      Synprs.Signature.Declaration.Raw_val
        { location; identifier; typ; expression }

    let program_decl =
      keyword "rec"
      &> seq4 (identifier <& colon) (comp_typ <& equals)
           (maybe (slash &> totality_declaration <& slash))
           comp_expression
      |> span
      $> fun (location, (identifier, typ, order, body)) ->
      Synprs.Signature.Declaration.Raw_theorem
        { location; identifier; typ; order; body }

    let proof_decl =
      keyword "proof"
      &> seq4 (identifier <& colon) (comp_typ <& equals)
           (maybe (slash &> totality_declaration <& slash))
           harpoon_proof
      |> span
      $> fun (location, (identifier, typ, order, body)) ->
      Synprs.Signature.Declaration.Raw_proof
        { location; identifier; typ; order; body }

    let signature_thm_decl =
      sep_by1 ~sep:(keyword "and") (choice [ program_decl; proof_decl ])
      <& semicolon |> span
      |> labelled "(mutual) recursive function declaration(s)"
      $> fun (location, declarations) ->
      Synprs.Signature.Declaration.Raw_recursive_declarations
        { location; declarations }

    let signature_module_decl =
      seq2
        (keyword "module" &> identifier)
        (equals &> keyword "struct" &> many Signature_parsers.signature_entry)
      <& keyword "end" <& maybe semicolon |> span
      |> labelled "module declaration"
      $> fun (location, (identifier, entries)) ->
      Synprs.Signature.Declaration.Raw_module
        { location; identifier; entries }

    let signature_declaration =
      choice
        [ signature_lf_typ_decl
        ; signature_oldstyle_lf_decl
        ; signature_cmp_typ_decl
        ; signature_schema_decl
        ; signature_module_decl
        ; signature_typedef_decl
        ; signature_let_decl
        ; signature_thm_decl
        ]

    let signature_pragma =
      choice
        [ name_pragma
        ; not_pragma
        ; fixity_pragma
        ; default_associativity_pragma
        ; open_pragma
        ; abbrev_pragma
        ; query_pragma
        ]

    let signature_entry =
      let declaration =
        signature_declaration |> span $> fun (location, declaration) ->
        Synprs.Signature.Entry.Raw_declaration { location; declaration }
      and pragma =
        signature_pragma |> span $> fun (location, pragma) ->
        Synprs.Signature.Entry.Raw_pragma { location; pragma }
      and comment =
        block_comment
        $> (fun (location, content) ->
             Synprs.Signature.Entry.Raw_comment { location; content })
        |> labelled "Block comment"
      in
      choice [ declaration; pragma; comment ]

    let signature =
      let* global_pragmas = many signature_global_pragma in
      let* entries = many signature_entry in
      return { Synprs.Signature.global_pragmas; entries }
  end

  let signature = Signature_parsers.signature

  let signature_global_pragma = Signature_parsers.signature_global_pragma

  let signature_entry = Signature_parsers.signature_entry

  let signature_declaration = Signature_parsers.signature_declaration

  let trust_totality_declaration =
    Signature_parsers.trust_totality_declaration

  let named_totality_declaration =
    Signature_parsers.named_totality_declaration

  let numeric_totality_declaration =
    Signature_parsers.numeric_totality_declaration

  let totality_declaration = Signature_parsers.totality_declaration
end
