open Support
open Beluga_syntax
open Common_parser

module rec Signature_parsers : sig
  val sgn : Synprs.Signature.t t

  val sgn_entry : Synprs.Signature.Entry.t t

  val sgn_declaration : Synprs.Signature.Declaration.t t

  val trust_totality_declaration : Synprs.Signature.Totality.Declaration.t t

  val named_totality_declaration : Synprs.Signature.Totality.Declaration.t t

  val numeric_totality_declaration :
    Synprs.Signature.Totality.Declaration.t t

  val totality_declaration : Synprs.Signature.Totality.Declaration.t t
end = struct
  let nostrenghten_pragma =
    pragma "nostrengthen" |> span $> fun (location, ()) ->
    Synprs.Signature.Global_pragma.No_strengthening { location }

  let coverage_pragma =
    pragma "coverage" |> span $> fun (location, ()) ->
    Synprs.Signature.Global_pragma.Raise_error_on_coverage_error { location }

  let warncoverage_pragma =
    pragma "warncoverage" |> span $> fun (location, ()) ->
    Synprs.Signature.Global_pragma.Warn_on_coverage_error { location }

  let sgn_global_prag =
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

  let sgn_lf_const_decl =
    seq2 (identifier <& colon) Lf_parser.lf_object
    |> span
    $> (fun (location, (identifier, typ)) ->
         Synprs.Signature.Declaration.Raw_lf_term_constant
           { location; identifier; typ })
    |> labelled "LF term-level constant declaration"

  let sgn_lf_typ_decl =
    let lf_typ_decl_body =
      let typ_decl = seq2 (identifier <& colon) Lf_parser.lf_object in
      seq2 (typ_decl <& equals) (maybe pipe &> sep_by0 sgn_lf_const_decl pipe)
      |> span
      $> fun (location, ((identifier, kind), constructor_declarations)) ->
      let typ_declaration =
        Synprs.Signature.Declaration.Raw_lf_typ_constant
          { location; identifier; kind }
      in
      List1.from typ_declaration constructor_declarations
    in
    keyword "LF"
    &> sep_by1 lf_typ_decl_body
         (keyword "and" &> maybe (keyword "LF") |> void)
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
      braces (some totality_argument) |> span $> fun (location, arguments) ->
      Synprs.Signature.Totality.Order.Lexical_ordering
        { location; arguments }
    and simultaneous_ordering =
      bracks (some totality_argument) |> span $> fun (location, arguments) ->
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
  let sgn_cmp_typ_decl =
    let cmp_typ_decl =
      let inductive = keyword "inductive" $> fun () -> `Inductive
      and stratified = keyword "stratified" $> fun () -> `Stratified in
      let flavour = choice [ inductive; stratified ] in
      let sgn_cmp_typ_decl_body =
        seq2 (identifier <& colon) Comp_parser.comp_sort_object |> span
        $> fun (location, (identifier, typ)) ->
        Synprs.Signature.Declaration.Raw_comp_expression_constructor
          { location; identifier; typ }
      in
      seq4 flavour (identifier <& colon)
        (Comp_parser.comp_sort_object <& equals <& maybe pipe)
        (sep_by0 sgn_cmp_typ_decl_body pipe)
      |> span
      $> fun ( location
             , (datatype_flavour, identifier, kind, constructor_declarations)
             ) ->
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
          (opt_parens
             (seq2 (identifier <& colon) Comp_parser.comp_sort_object)
          <& double_colon)
          Comp_parser.comp_sort_object
        |> span
        $> fun (location, ((identifier, observation_type), return_type)) ->
        Synprs.Signature.Declaration.Raw_comp_expression_destructor
          { location; identifier; observation_type; return_type }
      in
      seq3
        (keyword "coinductive" &> identifier <& colon)
        (Comp_parser.comp_sort_object <& equals <& maybe pipe)
        (sep_by0 cmp_cotyp_body pipe)
      |> span
      $> fun (location, (identifier, kind, destructor_declarations)) ->
      let cotyp_declaration =
        Synprs.Signature.Declaration.Raw_comp_cotyp_constant
          { location; identifier; kind }
      in
      List1.from cotyp_declaration destructor_declarations
    in
    sep_by1 (alt cmp_typ_decl cmp_cotyp_decl) (keyword "and")
    <& semicolon |> span
    $> (fun (location, declarations) ->
         let declarations' = List1.flatten declarations in
         Synprs.Signature.Declaration.Raw_recursive_declarations
           { location; declarations = declarations' })
    |> labelled "Inductive or stratified computation type declaration"

  let query_declaration =
    let bound =
      alt (star $> fun () -> Option.none) (integer $> Option.some)
      |> labelled "search bound"
    and meta_context =
      many
        (braces
           (seq2 meta_object_identifier
              (maybe (colon &> Meta_parser.meta_thing))))
      |> span
      $> fun (location, bindings) ->
      { Synprs.Meta.Context_object.location; bindings }
    in
    pragma "query"
    &> seq4 (seq2 bound bound) meta_context
         (maybe (identifier <& colon))
         Lf_parser.lf_object
    <& dot |> span
    |> labelled "logic programming engine query pragma"
    $> fun ( location
           , ( (expected_solutions, maximum_tries)
             , meta_context
             , identifier
             , typ ) ) ->
    Synprs.Signature.Declaration.Raw_query
      { location
      ; identifier
      ; meta_context
      ; typ
      ; expected_solutions
      ; maximum_tries
      }

  let mquery_declaration =
    let bound =
      alt (star $> fun () -> Option.none) (integer $> Option.some)
      |> labelled "search bound"
    in
    pragma "mquery"
    &> seq3 (seq3 bound bound bound)
         (maybe (identifier <& colon))
         Comp_parser.comp_sort_object
    <& dot |> span
    |> labelled "meta-logic search engine mquery pragma"
    $> fun ( location
           , ( (expected_solutions, search_tries, search_depth)
             , identifier
             , typ ) ) ->
    Synprs.Signature.Declaration.Raw_mquery
      { location
      ; identifier
      ; typ
      ; expected_solutions
      ; search_tries
      ; search_depth
      }

  let sgn_oldstyle_lf_decl =
    seq2 (identifier <& colon) Lf_parser.lf_object
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
    Synprs.Signature.Pragma.Prefix_fixity { location; constant; precedence }

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
    Synprs.Signature.Pragma.Postfix_fixity { location; constant; precedence }

  let fixity_pragma = choice [ prefix_pragma; infix_pragma; postfix_pragma ]

  let default_associativity_pragma =
    pragma "assoc" &> associativity <& dot |> span
    $> fun (location, associativity) ->
    Synprs.Signature.Pragma.Default_associativity { location; associativity }

  let open_pragma =
    pragma "open" &> qualified_identifier <& dot |> span
    $> (fun (location, module_identifier) ->
         Synprs.Signature.Pragma.Open_module { location; module_identifier })
    |> labelled "open module pragma"

  let abbrev_pragma =
    pragma "abbrev"
    &> seq2 qualified_identifier identifier
    <& dot |> span
    $> (fun (location, (module_identifier, abbreviation)) ->
         Synprs.Signature.Pragma.Abbreviation
           { location; module_identifier; abbreviation })
    |> labelled "module abbreviation pragma"

  let sgn_typedef_decl =
    seq3
      (keyword "typedef" &> identifier)
      (colon &> Comp_parser.comp_sort_object)
      (equals &> Comp_parser.comp_sort_object <& semicolon)
    |> span
    |> labelled "type synonym declaration"
    $> fun (location, (identifier, kind, typ)) ->
    Synprs.Signature.Declaration.Raw_comp_typ_abbreviation
      { location; identifier; kind; typ }

  let sgn_schema_decl =
    seq2 (keyword "schema" &> identifier <& equals) Meta_parser.schema_object
    <& semicolon |> span
    $> (fun (location, (identifier, schema)) ->
         Synprs.Signature.Declaration.Raw_schema
           { location; identifier; schema })
    |> labelled "Context schema declaration"

  let sgn_let_decl =
    seq2
      (keyword "let"
      &> seq2 identifier (maybe (colon &> Comp_parser.comp_sort_object)))
      (equals &> Comp_parser.comp_expression_object <& semicolon)
    |> span
    |> labelled "value declaration"
    $> fun (location, ((identifier, typ), expression)) ->
    Synprs.Signature.Declaration.Raw_val
      { location; identifier; typ; expression }

  let program_decl =
    seq4 (identifier <& colon)
      (Comp_parser.comp_sort_object <& equals)
      (maybe (slash &> totality_declaration <& slash))
      Comp_parser.comp_expression_object
    |> span
    $> fun (location, (identifier, typ, order, body)) ->
    Synprs.Signature.Declaration.Raw_theorem
      { location; identifier; typ; order; body }

  let proof_decl =
    keyword "proof"
    &> seq4 (identifier <& colon)
         (Comp_parser.comp_sort_object <& equals)
         (maybe (slash &> totality_declaration <& slash))
         Harpoon_parser.harpoon_proof
    |> span
    $> fun (location, (identifier, typ, order, body)) ->
    Synprs.Signature.Declaration.Raw_proof
      { location; identifier; typ; order; body }

  let sgn_thm_decl =
    keyword "rec"
    &> sep_by1 (choice [ program_decl; proof_decl ]) (keyword "and")
    <& semicolon |> span
    |> labelled "(mutual) recursive function declaration(s)"
    $> fun (location, declarations) ->
    Synprs.Signature.Declaration.Raw_recursive_declarations
      { location; declarations }

  let sgn_module_decl =
    seq2
      (keyword "module" &> identifier)
      (equals &> keyword "struct" &> many Signature_parsers.sgn_entry)
    <& keyword "end" <& maybe semicolon |> span
    |> labelled "module declaration"
    $> fun (location, (identifier, declarations)) ->
    Synprs.Signature.Declaration.Raw_module
      { location; identifier; declarations }

  let sgn_declaration =
    choice
      [ sgn_lf_typ_decl
      ; sgn_oldstyle_lf_decl
      ; sgn_cmp_typ_decl
      ; sgn_schema_decl
      ; sgn_module_decl
      ; sgn_typedef_decl
      ; sgn_let_decl
      ; sgn_thm_decl
      ; query_declaration
      ; mquery_declaration
      ]
    |> labelled "top-level declaration"

  let sgn_pragma =
    choice
      [ name_pragma
      ; not_pragma
      ; fixity_pragma
      ; default_associativity_pragma
      ; open_pragma
      ; abbrev_pragma
      ]
    |> labelled "pragma"

  let sgn_entry =
    let declaration =
      sgn_declaration |> span $> fun (location, declaration) ->
      Synprs.Signature.Entry.Raw_declaration { location; declaration }
    and pragma =
      sgn_pragma |> span $> fun (location, pragma) ->
      Synprs.Signature.Entry.Raw_pragma { location; pragma }
    and comment =
      block_comment
      $> (fun (location, content) ->
           Synprs.Signature.Entry.Raw_comment { location; content })
      |> labelled "HTML comment"
    in
    choice [ declaration; pragma; comment ]

  let sgn =
    seq2
      (many sgn_global_prag |> renamed "zero or more global pragmas")
      (many sgn_entry |> renamed "zero or more top-level declarations")
    $> fun (prags, decls) ->
    { Synprs.Signature.global_pragmas = prags; entries = decls }
end

let sgn = Signature_parsers.sgn

let sgn_entry = Signature_parsers.sgn_entry

let sgn_declaration = Signature_parsers.sgn_declaration

let trust_totality_declaration = Signature_parsers.trust_totality_declaration

let named_totality_declaration = Signature_parsers.named_totality_declaration

let numeric_totality_declaration =
  Signature_parsers.numeric_totality_declaration

let totality_declaration = Signature_parsers.totality_declaration
