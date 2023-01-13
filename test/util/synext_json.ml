(** JSON serialization for the external syntax.

    This is used to display parsed external syntax objects when parser tests
    fail. *)

open Support
open Beluga_syntax
open Synext
open Base_json

(** {1 Common} *)

let json_of_location location =
  if Location.is_ghost location then `Null
  else
    json_of_association
      [ ("filename", json_of_string (Location.filename location))
      ; ("start_line", json_of_int (Location.start_line location))
      ; ("start_column", json_of_int (Location.start_column location))
      ; ("stop_line", json_of_int (Location.stop_line location))
      ; ("stop_column", json_of_int (Location.stop_column location))
      ]

let json_of_identifier identifier =
  json_of_association
    [ ("name", json_of_string (Identifier.name identifier))
    ; ("location", json_of_location (Identifier.location identifier))
    ]

let json_of_qualified_identifier identifier =
  json_of_association
    [ ("name", json_of_identifier (Qualified_identifier.name identifier))
    ; ( "modules"
      , json_of_list json_of_identifier
          (Qualified_identifier.modules identifier) )
    ; ( "location"
      , json_of_location (Qualified_identifier.location identifier) )
    ]

let json_of_identifier_opt = json_of_option json_of_identifier

let json_of_qualified_identifier_opt =
  json_of_option json_of_qualified_identifier

let[@inline] json_of_plicity plicity =
  match plicity with
  | Plicity.Explicit -> json_of_string "explicit"
  | Plicity.Implicit -> json_of_string "implicit"

let[@inline] json_of_fixity fixity =
  match fixity with
  | Fixity.Prefix -> json_of_string "prefix"
  | Fixity.Infix -> json_of_string "infix"
  | Fixity.Postfix -> json_of_string "postfix"

let[@inline] json_of_associativity associativity =
  match associativity with
  | Associativity.Left_associative -> json_of_string "left-associative"
  | Associativity.Right_associative -> json_of_string "right-associative"
  | Associativity.Non_associative -> json_of_string "non-associative"

let json_of_operator operator =
  json_of_association
    [ ("fixity", json_of_fixity (Operator.fixity operator))
    ; ( "associativity"
      , json_of_associativity (Operator.associativity operator) )
    ; ("arity", json_of_int (Operator.arity operator))
    ; ("precedence", json_of_int (Operator.precedence operator))
    ]

(** {1 LF} *)

let rec json_of_lf_kind kind =
  match kind with
  | LF.Kind.Typ { location } ->
      json_of_variant ~name:"LF.Kind.Typ"
        ~data:[ ("location", json_of_location location) ]
  | LF.Kind.Arrow { domain; range; location } ->
      json_of_variant ~name:"LF.Kind.Arrow"
        ~data:
          [ ("domain", json_of_lf_typ domain)
          ; ("range", json_of_lf_kind range)
          ; ("location", json_of_location location)
          ]
  | LF.Kind.Pi { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"LF.Kind.Pi"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_option json_of_lf_typ parameter_type)
          ; ("body", json_of_lf_kind body)
          ; ("location", json_of_location location)
          ]

and json_of_lf_typ typ =
  match typ with
  | LF.Typ.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"LF.Typ.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | LF.Typ.Application { applicand; arguments; location } ->
      json_of_variant ~name:"LF.Typ.Application"
        ~data:
          [ ("applicand", json_of_lf_typ applicand)
          ; ("arguments", json_of_list1 json_of_lf_term arguments)
          ; ("location", json_of_location location)
          ]
  | LF.Typ.Arrow { domain; range; orientation; location } ->
      json_of_variant ~name:"LF.Typ.Arrow"
        ~data:
          [ ("domain", json_of_lf_typ domain)
          ; ("range", json_of_lf_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> json_of_string "forward"
              | `Backward -> json_of_string "backward" )
          ; ("location", json_of_location location)
          ]
  | LF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"LF.Typ.Pi"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_option json_of_lf_typ parameter_type)
          ; ("body", json_of_lf_typ body)
          ; ("location", json_of_location location)
          ]

and json_of_lf_term term =
  match term with
  | LF.Term.Variable { identifier; location } ->
      json_of_variant ~name:"LF.Term.Variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | LF.Term.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"LF.Term.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | LF.Term.Application { applicand; arguments; location } ->
      json_of_variant ~name:"LF.Term.Application"
        ~data:
          [ ("applicand", json_of_lf_term applicand)
          ; ("arguments", json_of_list1 json_of_lf_term arguments)
          ; ("location", json_of_location location)
          ]
  | LF.Term.Abstraction
      { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"LF.Term.Abstraction"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_option json_of_lf_typ parameter_type)
          ; ("body", json_of_lf_term body)
          ; ("location", json_of_location location)
          ]
  | LF.Term.Wildcard { location } ->
      json_of_variant ~name:"LF.Term.Wildcard"
        ~data:[ ("location", json_of_location location) ]
  | LF.Term.TypeAnnotated { term; typ; location } ->
      json_of_variant ~name:"LF.Term.TypeAnnotated"
        ~data:
          [ ("term", json_of_lf_term term)
          ; ("typ", json_of_lf_typ typ)
          ; ("location", json_of_location location)
          ]

(** {1 Contextual LF} *)

let rec json_of_clf_typ typ =
  match typ with
  | CLF.Typ.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"CLF.Typ.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | CLF.Typ.Application { applicand; arguments; location } ->
      json_of_variant ~name:"CLF.Typ.Application"
        ~data:
          [ ("applicand", json_of_clf_typ applicand)
          ; ("arguments", json_of_list1 json_of_clf_term arguments)
          ; ("location", json_of_location location)
          ]
  | CLF.Typ.Arrow { domain; range; orientation; location } ->
      json_of_variant ~name:"CLF.Typ.Arrow"
        ~data:
          [ ("domain", json_of_clf_typ domain)
          ; ("range", json_of_clf_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> json_of_string "forward"
              | `Backward -> json_of_string "backward" )
          ; ("location", json_of_location location)
          ]
  | CLF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"CLF.Typ.Pi"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_clf_typ parameter_type)
          ; ("body", json_of_clf_typ body)
          ; ("location", json_of_location location)
          ]
  | CLF.Typ.Block { elements; location } ->
      json_of_variant ~name:"CLF.Typ.Block"
        ~data:
          [ ( "elements"
            , match elements with
              | `Unnamed typ -> json_of_clf_typ typ
              | `Record bindings ->
                  json_of_list1
                    (fun (identifier, typ) ->
                      json_of_association
                        [ ("identifier", json_of_identifier identifier)
                        ; ("typ", json_of_clf_typ typ)
                        ])
                    bindings )
          ; ("location", json_of_location location)
          ]

and json_of_clf_term term =
  match term with
  | CLF.Term.Variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Parameter_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Parameter_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Substitution_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Substitution_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"CLF.Term.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Application { applicand; arguments; location } ->
      json_of_variant ~name:"CLF.Term.Application"
        ~data:
          [ ("applicand", json_of_clf_term applicand)
          ; ("arguments", json_of_list1 json_of_clf_term arguments)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Abstraction
      { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"CLF.Term.Abstraction"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_option json_of_clf_typ parameter_type)
          ; ("body", json_of_clf_term body)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.TypeAnnotated { term; typ; location } ->
      json_of_variant ~name:"CLF.Term.TypeAnnotated"
        ~data:
          [ ("term", json_of_clf_term term)
          ; ("typ", json_of_clf_typ typ)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Hole { variant; location } ->
      json_of_variant ~name:"CLF.Term.Hole"
        ~data:
          [ ( "variant"
            , match variant with
              | `Underscore -> json_of_string "underscore"
              | `Unlabelled -> json_of_string "unlabelled"
              | `Labelled label ->
                  json_of_association [ ("label", json_of_identifier label) ]
            )
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Tuple { terms; location } ->
      json_of_variant ~name:"CLF.Term.Tuple"
        ~data:
          [ ("elements", json_of_list1 json_of_clf_term terms)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Projection { term; projection; location } ->
      json_of_variant ~name:"CLF.Term.Projection"
        ~data:
          [ ("term", json_of_clf_term term)
          ; ( "projection"
            , match projection with
              | `By_identifier identifier -> json_of_identifier identifier
              | `By_position index -> json_of_int index )
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Substitution { term; substitution; location } ->
      json_of_variant ~name:"CLF.Term.Substitution"
        ~data:
          [ ("term", json_of_clf_term term)
          ; ("substitution", json_of_clf_substitution substitution)
          ; ("location", json_of_location location)
          ]

and json_of_clf_term_pattern term_pattern =
  match term_pattern with
  | CLF.Term.Pattern.Variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Parameter_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Parameter_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Substitution_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Substitution_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"CLF.Term.Pattern.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Application { applicand; arguments; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Application"
        ~data:
          [ ("applicand", json_of_clf_term_pattern applicand)
          ; ("arguments", json_of_list1 json_of_clf_term_pattern arguments)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Abstraction
      { parameter_identifier; parameter_type; body; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Abstraction"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("parameter_type", json_of_option json_of_clf_typ parameter_type)
          ; ("body", json_of_clf_term_pattern body)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.TypeAnnotated { term; typ; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.TypeAnnotated"
        ~data:
          [ ("term", json_of_clf_term_pattern term)
          ; ("typ", json_of_clf_typ typ)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Wildcard { location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Wildcard"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Term.Pattern.Tuple { terms; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Tuple"
        ~data:
          [ ("elements", json_of_list1 json_of_clf_term_pattern terms)
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Projection { term; projection; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Projection"
        ~data:
          [ ("term", json_of_clf_term_pattern term)
          ; ( "projection"
            , match projection with
              | `By_identifier identifier -> json_of_identifier identifier
              | `By_position index -> json_of_int index )
          ; ("location", json_of_location location)
          ]
  | CLF.Term.Pattern.Substitution { term; substitution; location } ->
      json_of_variant ~name:"CLF.Term.Pattern.Substitution"
        ~data:
          [ ("term", json_of_clf_term_pattern term)
          ; ("substitution", json_of_clf_substitution substitution)
          ; ("location", json_of_location location)
          ]

and json_of_clf_substitution substition =
  match substition with
  | { CLF.Substitution.head; terms; location } ->
      json_of_variant ~name:"CLF.Substitution"
        ~data:
          [ ("head", json_of_clf_substitution_head head)
          ; ("terms", json_of_list json_of_clf_term terms)
          ; ("location", json_of_location location)
          ]

and json_of_clf_substitution_head head =
  match head with
  | CLF.Substitution.Head.None { location } ->
      json_of_variant ~name:"CLF.Substitution.Head.None"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Substitution.Head.Identity { location } ->
      json_of_variant ~name:"CLF.Substitution.Head.Identity"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Substitution.Head.Substitution_variable
      { identifier; closure; location } ->
      json_of_variant ~name:"CLF.Substitution.Head.Substitution_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("closure", json_of_option json_of_clf_substitution closure)
          ; ("location", json_of_location location)
          ]

and json_of_clf_substitution_pattern substitution_pattern =
  match substitution_pattern with
  | { CLF.Substitution.Pattern.head; terms; location } ->
      json_of_variant ~name:"CLF.Substitution"
        ~data:
          [ ("head", json_of_clf_substitution_pattern_head head)
          ; ("terms", json_of_list json_of_clf_term_pattern terms)
          ; ("location", json_of_location location)
          ]

and json_of_clf_substitution_pattern_head head =
  match head with
  | CLF.Substitution.Pattern.Head.None { location } ->
      json_of_variant ~name:"CLF.Substitution.Pattern.Head.None"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Substitution.Pattern.Head.Identity { location } ->
      json_of_variant ~name:"CLF.Substitution.Pattern.Head.Identity"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Substitution.Pattern.Head.Substitution_variable
      { identifier; closure; location } ->
      json_of_variant
        ~name:"CLF.Substitution.Pattern.Head.Substitution_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("closure", json_of_option json_of_clf_substitution closure)
          ; ("location", json_of_location location)
          ]

and json_of_clf_context context =
  match context with
  | { CLF.Context.head; bindings; location } ->
      json_of_variant ~name:"CLF.Context"
        ~data:
          [ ("head", json_of_clf_context_head head)
          ; ( "bindings"
            , json_of_list
                (fun (identifier, typ) ->
                  json_of_association
                    [ ("identifier", json_of_identifier identifier)
                    ; ("typ", json_of_option json_of_clf_typ typ)
                    ])
                bindings )
          ; ("location", json_of_location location)
          ]

and json_of_clf_context_head head =
  match head with
  | CLF.Context.Head.None { location } ->
      json_of_variant ~name:"CLF.Context.Head.None"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Context.Head.Hole { location } ->
      json_of_variant ~name:"CLF.Context.Head.Hole"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Context.Head.Context_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Context.Head.Context_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]

and json_of_clf_context_pattern context_pattern =
  match context_pattern with
  | { CLF.Context.Pattern.head; bindings; location } ->
      json_of_variant ~name:"CLF.Context.Pattern"
        ~data:
          [ ("head", json_of_clf_context_pattern_head head)
          ; ( "bindings"
            , json_of_list
                (fun (identifier, typ) ->
                  json_of_association
                    [ ("identifier", json_of_identifier identifier)
                    ; ("typ", json_of_clf_typ typ)
                    ])
                bindings )
          ; ("location", json_of_location location)
          ]

and json_of_clf_context_pattern_head head =
  match head with
  | CLF.Context.Pattern.Head.None { location } ->
      json_of_variant ~name:"CLF.Context.Head.Pattern.None"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Context.Pattern.Head.Hole { location } ->
      json_of_variant ~name:"CLF.Context.Head.Pattern.Hole"
        ~data:[ ("location", json_of_location location) ]
  | CLF.Context.Pattern.Head.Context_variable { identifier; location } ->
      json_of_variant ~name:"CLF.Context.Pattern.Head.Context_variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]

(** {1 Meta-Level} *)

let rec json_of_meta_typ typ =
  match typ with
  | Meta.Typ.Context_schema { schema; location } ->
      json_of_variant ~name:"Meta.Typ.Context_schema"
        ~data:
          [ ("schema", json_of_schema schema)
          ; ("location", json_of_location location)
          ]
  | Meta.Typ.Contextual_typ { context; typ; location } ->
      json_of_variant ~name:"Meta.Typ.Contextual_typ"
        ~data:
          [ ("context", json_of_clf_context context)
          ; ("typ", json_of_clf_typ typ)
          ; ("location", json_of_location location)
          ]
  | Meta.Typ.Parameter_typ { context; typ; location } ->
      json_of_variant ~name:"Meta.Typ.Parameter_typ"
        ~data:
          [ ("context", json_of_clf_context context)
          ; ("typ", json_of_clf_typ typ)
          ; ("location", json_of_location location)
          ]
  | Meta.Typ.Plain_substitution_typ { domain; range; location } ->
      json_of_variant ~name:"Meta.Typ.Plain_substitution_typ"
        ~data:
          [ ("domain", json_of_clf_context domain)
          ; ("range", json_of_clf_context range)
          ; ("location", json_of_location location)
          ]
  | Meta.Typ.Renaming_substitution_typ { domain; range; location } ->
      json_of_variant ~name:"Meta.Typ.Renaming_substitution_typ"
        ~data:
          [ ("domain", json_of_clf_context domain)
          ; ("range", json_of_clf_context range)
          ; ("location", json_of_location location)
          ]

and json_of_meta_object object_ =
  match object_ with
  | Meta.Object.Context { context; location } ->
      json_of_variant ~name:"Meta.Object.Context"
        ~data:
          [ ("context", json_of_clf_context context)
          ; ("location", json_of_location location)
          ]
  | Meta.Object.Contextual_term { context; term; location } ->
      json_of_variant ~name:"Meta.Object.Contextual_term"
        ~data:
          [ ("context", json_of_clf_context context)
          ; ("term", json_of_clf_term term)
          ; ("location", json_of_location location)
          ]
  | Meta.Object.Plain_substitution { domain; range; location } ->
      json_of_variant ~name:"Meta.Object.Plain_substitution"
        ~data:
          [ ("domain", json_of_clf_context domain)
          ; ("range", json_of_clf_substitution range)
          ; ("location", json_of_location location)
          ]
  | Meta.Object.Renaming_substitution { domain; range; location } ->
      json_of_variant ~name:"Meta.Object.Renaming_substitution"
        ~data:
          [ ("domain", json_of_clf_context domain)
          ; ("range", json_of_clf_substitution range)
          ; ("location", json_of_location location)
          ]

and json_of_meta_pattern pattern =
  match pattern with
  | Meta.Pattern.Context { context; location } ->
      json_of_variant ~name:"Meta.Pattern.Context"
        ~data:
          [ ("context", json_of_clf_context_pattern context)
          ; ("location", json_of_location location)
          ]
  | Meta.Pattern.Contextual_term { context; term; location } ->
      json_of_variant ~name:"Meta.Pattern.Contextual_term"
        ~data:
          [ ("context", json_of_clf_context_pattern context)
          ; ("term", json_of_clf_term_pattern term)
          ; ("location", json_of_location location)
          ]
  | Meta.Pattern.Plain_substitution { domain; range; location } ->
      json_of_variant ~name:"Meta.Pattern.Plain_substitution"
        ~data:
          [ ("domain", json_of_clf_context_pattern domain)
          ; ("range", json_of_clf_substitution_pattern range)
          ; ("location", json_of_location location)
          ]
  | Meta.Pattern.Renaming_substitution { domain; range; location } ->
      json_of_variant ~name:"Meta.Pattern.Renaming_substitution"
        ~data:
          [ ("domain", json_of_clf_context_pattern domain)
          ; ("range", json_of_clf_substitution_pattern range)
          ; ("location", json_of_location location)
          ]

and json_of_meta_context context =
  match context with
  | { Meta.Context.bindings; location } ->
      json_of_variant ~name:"Meta.Context"
        ~data:
          [ ( "bindings"
            , json_of_list
                (fun (identifier, typ) ->
                  json_of_association
                    [ ("identifier", json_of_identifier identifier)
                    ; ("typ", json_of_meta_typ typ)
                    ])
                bindings )
          ; ("location", json_of_location location)
          ]

and json_of_schema schema =
  match schema with
  | Meta.Schema.Constant { identifier; location } ->
      json_of_variant ~name:"Meta.Schema.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | Meta.Schema.Alternation { schemas; location } ->
      json_of_variant ~name:"Meta.Schema.Alternation"
        ~data:
          [ ("schemas", json_of_list2 json_of_schema schemas)
          ; ("location", json_of_location location)
          ]
  | Meta.Schema.Element { some; block; location } ->
      json_of_variant ~name:"Meta.Schema.Element"
        ~data:
          [ ( "some"
            , json_of_option
                (json_of_list1 (fun (identifier, typ) ->
                     json_of_association
                       [ ("identifier", json_of_identifier identifier)
                       ; ("typ", json_of_clf_typ typ)
                       ]))
                some )
          ; ( "block"
            , match block with
              | `Unnamed typ -> json_of_clf_typ typ
              | `Record bindings ->
                  json_of_list1
                    (fun (identifier, typ) ->
                      json_of_association
                        [ ("identifier", json_of_identifier identifier)
                        ; ("typ", json_of_clf_typ typ)
                        ])
                    bindings )
          ; ("location", json_of_location location)
          ]

(** {1 Computation-Level} *)

let rec json_of_comp_kind kind =
  match kind with
  | Comp.Kind.Ctype { location } ->
      json_of_variant ~name:"Comp.Kind.Ctype"
        ~data:[ ("location", json_of_location location) ]
  | Comp.Kind.Arrow { domain; range; location } ->
      json_of_variant ~name:"Comp.Kind.Arrow"
        ~data:
          [ ("domain", json_of_meta_typ domain)
          ; ("range", json_of_comp_kind range)
          ; ("location", json_of_location location)
          ]
  | Comp.Kind.Pi
      { parameter_identifier; plicity; parameter_type; body; location } ->
      json_of_variant ~name:"Comp.Kind.Pi"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("plicity", json_of_plicity plicity)
          ; ("parameter_type", json_of_meta_typ parameter_type)
          ; ("body", json_of_comp_kind body)
          ; ("location", json_of_location location)
          ]

and json_of_comp_typ typ =
  match typ with
  | Comp.Typ.Constant { identifier; quoted; location; operator; variant } ->
      json_of_variant ~name:"Comp.Typ.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ( "variant"
            , match variant with
              | `Inductive -> json_of_string "inductive"
              | `Stratified -> json_of_string "Stratified"
              | `Abbreviation -> json_of_string "abbreviation"
              | `Coinductive -> json_of_string "coinductive" )
          ; ("location", json_of_location location)
          ]
  | Comp.Typ.Pi
      { parameter_identifier; plicity; parameter_type; body; location } ->
      json_of_variant ~name:"Comp.Typ.Pi"
        ~data:
          [ ( "parameter_identifier"
            , json_of_identifier_opt parameter_identifier )
          ; ("plicity", json_of_plicity plicity)
          ; ("parameter_type", json_of_meta_typ parameter_type)
          ; ("body", json_of_comp_typ body)
          ; ("location", json_of_location location)
          ]
  | Comp.Typ.Arrow { domain; range; orientation; location } ->
      json_of_variant ~name:"Comp.Typ.Arrow"
        ~data:
          [ ("domain", json_of_comp_typ domain)
          ; ("range", json_of_comp_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> json_of_string "forward"
              | `Backward -> json_of_string "backward" )
          ; ("location", json_of_location location)
          ]
  | Comp.Typ.Cross { types; location } ->
      json_of_variant ~name:"Comp.Typ.Cross"
        ~data:
          [ ("types", json_of_list2 json_of_comp_typ types)
          ; ("location", json_of_location location)
          ]
  | Comp.Typ.Box { meta_type; location } ->
      json_of_variant ~name:"Comp.Typ.Box"
        ~data:
          [ ("meta_type", json_of_meta_typ meta_type)
          ; ("location", json_of_location location)
          ]
  | Comp.Typ.Application { applicand; arguments; location } ->
      json_of_variant ~name:"Comp.Typ.Application"
        ~data:
          [ ("applicand", json_of_comp_typ applicand)
          ; ("arguments", json_of_list1 json_of_meta_object arguments)
          ; ("location", json_of_location location)
          ]

and json_of_comp_expression expression =
  match expression with
  | Comp.Expression.Variable { identifier; location } ->
      json_of_variant ~name:"Comp.Expression.Variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"Comp.Expression.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Fn { parameters; body; location } ->
      json_of_variant ~name:"Comp.Expression.Fn"
        ~data:
          [ ("parameters", json_of_list1 json_of_identifier_opt parameters)
          ; ("body", json_of_comp_expression body)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Mlam { parameters; body; location } ->
      json_of_variant ~name:"Comp.Expression.Mlam"
        ~data:
          [ ( "parameters"
            , json_of_list1
                Fun.(Pair.fst >> json_of_identifier_opt)
                parameters )
          ; ("body", json_of_comp_expression body)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Fun { branches; location } ->
      json_of_variant ~name:"Comp.Expression.Fun"
        ~data:
          [ ( "branches"
            , json_of_list1
                (fun (copatterns, body) ->
                  json_of_association
                    [ ( "patterns"
                      , json_of_list1 json_of_comp_copattern copatterns )
                    ; ("body", json_of_comp_expression body)
                    ])
                branches )
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Let { pattern; scrutinee; body; location } ->
      json_of_variant ~name:"Comp.Expression.Let"
        ~data:
          [ ("pattern", json_of_comp_pattern pattern)
          ; ("scrutinee", json_of_comp_expression scrutinee)
          ; ("body", json_of_comp_expression body)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Box { meta_object; location } ->
      json_of_variant ~name:"Comp.Expression.Box"
        ~data:
          [ ("meta_object", json_of_meta_object meta_object)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Impossible { scrutinee; location } ->
      json_of_variant ~name:"Comp.Expression.Impossible"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Case { scrutinee; check_coverage; branches; location } ->
      json_of_variant ~name:"Comp.Expression.Case"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("check_coverage", json_of_bool check_coverage)
          ; ( "branches"
            , json_of_list1
                (fun (pattern, body) ->
                  json_of_association
                    [ ("pattern", json_of_comp_pattern pattern)
                    ; ("body", json_of_comp_expression body)
                    ])
                branches )
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Tuple { elements; location } ->
      json_of_variant ~name:"Comp.Expression.Tuple"
        ~data:
          [ ("elements", json_of_list2 json_of_comp_expression elements)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Hole { label; location } ->
      json_of_variant ~name:"Comp.Expression.Hole"
        ~data:
          [ ("label", json_of_identifier_opt label)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.BoxHole { location } ->
      json_of_variant ~name:"Comp.Expression.BoxHole"
        ~data:[ ("location", json_of_location location) ]
  | Comp.Expression.Application { applicand; arguments; location } ->
      json_of_variant ~name:"Comp.Expression.Application"
        ~data:
          [ ("applicand", json_of_comp_expression applicand)
          ; ("arguments", json_of_list1 json_of_comp_expression arguments)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.Observation { location; scrutinee; destructor } ->
      json_of_variant ~name:"Comp.Expression.Observation"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("destructor", json_of_qualified_identifier destructor)
          ; ("location", json_of_location location)
          ]
  | Comp.Expression.TypeAnnotated { expression; typ; location } ->
      json_of_variant ~name:"Comp.Expression.TypeAnnotated"
        ~data:
          [ ("expression", json_of_comp_expression expression)
          ; ("typ", json_of_comp_typ typ)
          ; ("location", json_of_location location)
          ]

and json_of_comp_pattern pattern =
  match pattern with
  | Comp.Pattern.Variable { identifier; location } ->
      json_of_variant ~name:"Comp.Pattern.Variable"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.Constant { identifier; quoted; location; operator } ->
      json_of_variant ~name:"Comp.Pattern.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("quoted", json_of_bool quoted)
          ; ("operator", json_of_operator operator)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.MetaObject { meta_pattern; location } ->
      json_of_variant ~name:"Comp.Pattern.MetaObject"
        ~data:
          [ ("meta_pattern", json_of_meta_pattern meta_pattern)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.Tuple { elements; location } ->
      json_of_variant ~name:"Comp.Pattern.Tuple"
        ~data:
          [ ("elements", json_of_list2 json_of_comp_pattern elements)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.Application { applicand; arguments; location } ->
      json_of_variant ~name:"Comp.Pattern.Application"
        ~data:
          [ ("applicand", json_of_comp_pattern applicand)
          ; ("arguments", json_of_list1 json_of_comp_pattern arguments)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.TypeAnnotated { pattern; typ; location } ->
      json_of_variant ~name:"Comp.Pattern.TypeAnnotated"
        ~data:
          [ ("pattern", json_of_comp_pattern pattern)
          ; ("typ", json_of_comp_typ typ)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.MetaTypeAnnotated
      { annotation_identifier; annotation_type; body; location } ->
      json_of_variant ~name:"Comp.Pattern.MetaTypeAnnotated"
        ~data:
          [ ( "annotation_identifier"
            , json_of_identifier annotation_identifier )
          ; ("annotation_type", json_of_meta_typ annotation_type)
          ; ("body", json_of_comp_pattern body)
          ; ("location", json_of_location location)
          ]
  | Comp.Pattern.Wildcard { location } ->
      json_of_variant ~name:"Comp.Pattern.Wildcard"
        ~data:[ ("location", json_of_location location) ]

and json_of_comp_copattern pattern =
  match pattern with
  | Comp.Copattern.Pattern pattern -> json_of_comp_pattern pattern
  | Comp.Copattern.Observation { observation; arguments; location } ->
      json_of_variant ~name:"Comp.Copattern.Observation"
        ~data:
          [ ("observation", json_of_qualified_identifier observation)
          ; ("arguments", json_of_list json_of_comp_pattern arguments)
          ; ("location", json_of_location location)
          ]

and json_of_comp_context context =
  match context with
  | { Comp.Context.bindings; location } ->
      json_of_variant ~name:"Comp.Context"
        ~data:
          [ ( "bindings"
            , json_of_list
                (fun (identifier, typ) ->
                  json_of_association
                    [ ("identifier", json_of_identifier identifier)
                    ; ("typ", json_of_comp_typ typ)
                    ])
                bindings )
          ; ("location", json_of_location location)
          ]

(** {1 Harpoon} *)

let rec json_of_harpoon_proof proof =
  match proof with
  | Harpoon.Proof.Incomplete { label; location } ->
      json_of_variant ~name:"Harpoon.Proof.Incomplete"
        ~data:
          [ ("label", json_of_identifier_opt label)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Proof.Command { command; body; location } ->
      json_of_variant ~name:"Harpoon.Proof.Command"
        ~data:
          [ ("command", json_of_harpoon_command command)
          ; ("body", json_of_harpoon_proof body)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Proof.Directive { directive; location } ->
      json_of_variant ~name:"Harpoon.Proof.Directive"
        ~data:
          [ ("directive", json_of_harpoon_directive directive)
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_command command =
  match command with
  | Harpoon.Command.By { expression; assignee; location } ->
      json_of_variant ~name:"Harpoon.Command.By"
        ~data:
          [ ("expression", json_of_comp_expression expression)
          ; ("assignee", json_of_identifier assignee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Command.Unbox { expression; assignee; modifier; location } ->
      json_of_variant ~name:"Harpoon.Command.Unbox"
        ~data:
          [ ("expression", json_of_comp_expression expression)
          ; ("assignee", json_of_identifier assignee)
          ; ( "modifier"
            , match modifier with
              | Option.Some `Strengthened -> json_of_string "strengthened"
              | Option.None -> `Null )
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_directive directive =
  match directive with
  | Harpoon.Directive.Intros { hypothetical; location } ->
      json_of_variant ~name:"Harpoon.Directive.Intros"
        ~data:
          [ ("hypothetical", json_of_harpoon_hypothetical hypothetical)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Directive.Solve { solution; location } ->
      json_of_variant ~name:"Harpoon.Directive.Solve"
        ~data:
          [ ("solution", json_of_comp_expression solution)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Directive.Split { scrutinee; branches; location } ->
      json_of_variant ~name:"Harpoon.Directive.Split"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("branches", json_of_list1 json_of_harpoon_split_branch branches)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Directive.Impossible { scrutinee; location } ->
      json_of_variant ~name:"Harpoon.Directive.Impossible"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Directive.Suffices { scrutinee; branches; location } ->
      json_of_variant ~name:"Harpoon.Directive.Suffices"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ( "branches"
            , json_of_list json_of_harpoon_suffices_branch branches )
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_split_branch split_branch =
  match split_branch with
  | { Harpoon.Split_branch.label; body; location } ->
      json_of_variant ~name:"Harpoon.Split_branch"
        ~data:
          [ ("label", json_of_harpoon_split_branch_label label)
          ; ("body", json_of_harpoon_hypothetical body)
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_split_branch_label split_branch_label =
  match split_branch_label with
  | Harpoon.Split_branch.Label.Constant { identifier; location } ->
      json_of_variant ~name:"Harpoon.Split_branch.Label.Constant"
        ~data:
          [ ("identifier", json_of_qualified_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Split_branch.Label.Bound_variable { location } ->
      json_of_variant ~name:"Harpoon.Split_branch.Label.Bound_variable"
        ~data:[ ("location", json_of_location location) ]
  | Harpoon.Split_branch.Label.Empty_context { location } ->
      json_of_variant ~name:"Harpoon.Split_branch.Label.Empty_context"
        ~data:[ ("location", json_of_location location) ]
  | Harpoon.Split_branch.Label.Extended_context { schema_element; location }
    ->
      json_of_variant ~name:"Harpoon.Split_branch.Label.Extended_context"
        ~data:
          [ ("schema_element", json_of_int schema_element)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Split_branch.Label.Parameter_variable
      { schema_element; projection; location } ->
      json_of_variant ~name:"Harpoon.Split_branch.Label.Parameter_variable"
        ~data:
          [ ("schema_element", json_of_int schema_element)
          ; ("projection", json_of_option json_of_int projection)
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_suffices_branch suffices_branch =
  match suffices_branch with
  | { Harpoon.Suffices_branch.goal; proof; location } ->
      json_of_variant ~name:"Harpoon.Suffices_branch"
        ~data:
          [ ("goal", json_of_comp_typ goal)
          ; ("proof", json_of_harpoon_proof proof)
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_hypothetical hypothetical =
  match hypothetical with
  | { Harpoon.Hypothetical.meta_context; comp_context; proof; location } ->
      json_of_variant ~name:"Harpoon.Hypothetical"
        ~data:
          [ ("meta_context", json_of_meta_context meta_context)
          ; ("comp_context", json_of_comp_context comp_context)
          ; ("proof", json_of_harpoon_proof proof)
          ; ("location", json_of_location location)
          ]

and json_of_harpoon_repl_command command =
  match command with
  | Harpoon.Repl.Command.Rename { rename_from; rename_to; level; location }
    ->
      json_of_variant ~name:"Harpoon.Repl.Command.Rename"
        ~data:
          [ ("rename_from", json_of_identifier rename_from)
          ; ("rename_to", json_of_identifier rename_to)
          ; ( "level"
            , match level with
              | `meta -> json_of_string "meta"
              | `comp -> json_of_string "comp" )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Toggle_automation { kind; change; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Toggle_automation"
        ~data:
          [ ( "kind"
            , match kind with
              | `auto_intros -> json_of_string "auto_intros"
              | `auto_solve_trivial -> json_of_string " auto_solve_trivial"
            )
          ; ( "change"
            , match change with
              | `off -> json_of_string "off"
              | `on -> json_of_string "on"
              | `toggle -> json_of_string "toggle" )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Type { scrutinee; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Type"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Info { kind; object_identifier; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Info"
        ~data:
          [ ( "kind"
            , match kind with
              | `prog -> json_of_string "prog" )
          ; ( "object_identifier"
            , json_of_qualified_identifier object_identifier )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Select_theorem { theorem; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Select_theorem"
        ~data:
          [ ("theorem", json_of_qualified_identifier theorem)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Theorem { subcommand; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Theorem"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `defer -> json_of_string "defer"
              | `dump_proof file -> json_of_string file
              | `list -> json_of_string "list"
              | `show_ihs -> json_of_string "show_ihs"
              | `show_proof -> json_of_string "show_proof" )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Session { subcommand; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Session"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `create -> json_of_string "create"
              | `defer -> json_of_string "defer"
              | `list -> json_of_string "list"
              | `serialize -> json_of_string "serialize" )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Subgoal { subcommand; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Subgoal"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `defer -> json_of_string "defer"
              | `list -> json_of_string "list" )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Undo { location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Undo"
        ~data:[ ("location", json_of_location location) ]
  | Harpoon.Repl.Command.Redo { location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Redo"
        ~data:[ ("location", json_of_location location) ]
  | Harpoon.Repl.Command.History { location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.History"
        ~data:[ ("location", json_of_location location) ]
  | Harpoon.Repl.Command.Translate { theorem; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Translate"
        ~data:
          [ ("theorem", json_of_qualified_identifier theorem)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Intros { introduced_variables; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Intros"
        ~data:
          [ ( "introduced_variables"
            , json_of_option
                (json_of_list1 json_of_identifier)
                introduced_variables )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Split { scrutinee; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Split"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Invert { scrutinee; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Invert"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Impossible { scrutinee; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Impossible"
        ~data:
          [ ("scrutinee", json_of_comp_expression scrutinee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Msplit { identifier; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Msplit"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Solve { solution; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Solve"
        ~data:
          [ ("solution", json_of_comp_expression solution)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Unbox { expression; assignee; modifier; location }
    ->
      json_of_variant ~name:"Harpoon.Repl.Command.Unbox"
        ~data:
          [ ("expression", json_of_comp_expression expression)
          ; ("assignee", json_of_identifier assignee)
          ; ( "modifier"
            , json_of_option
                (function
                  | `Strengthened -> json_of_string "strengthened")
                modifier )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.By { expression; assignee; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.By"
        ~data:
          [ ("expression", json_of_comp_expression expression)
          ; ("assignee", json_of_identifier assignee)
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Suffices { implication; goal_premises; location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Suffices"
        ~data:
          [ ("implication", json_of_comp_expression implication)
          ; ( "goal_premises"
            , json_of_list
                (function
                  | `exact typ -> json_of_comp_typ typ
                  | `infer location -> json_of_location location)
                goal_premises )
          ; ("location", json_of_location location)
          ]
  | Harpoon.Repl.Command.Help { location } ->
      json_of_variant ~name:"Harpoon.Repl.Command.Help"
        ~data:[ ("location", json_of_location location) ]

(** {1 Signature} *)

let rec json_of_signature_pragma pragma =
  match pragma with
  | Signature.Pragma.Name
      { constant; meta_variable_base; computation_variable_base; location }
    ->
      json_of_variant ~name:"Signature.Pragma.Name"
        ~data:
          [ ("constant", json_of_qualified_identifier constant)
          ; ("meta_variable_base", json_of_identifier meta_variable_base)
          ; ( "computation_variable_base"
            , json_of_option json_of_identifier computation_variable_base )
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Default_associativity { associativity; location } ->
      json_of_variant ~name:"Signature.Pragma.Default_associativity"
        ~data:
          [ ("associativity", json_of_associativity associativity)
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Prefix_fixity { constant; precedence; location } ->
      json_of_variant ~name:"Signature.Pragma.Prefix_fixity"
        ~data:
          [ ("constant", json_of_qualified_identifier constant)
          ; ("precedence", json_of_option json_of_int precedence)
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Infix_fixity
      { constant; precedence; associativity; location } ->
      json_of_variant ~name:"Signature.Pragma.Infix_fixity"
        ~data:
          [ ("constant", json_of_qualified_identifier constant)
          ; ( "associativity"
            , json_of_option json_of_associativity associativity )
          ; ("precedence", json_of_option json_of_int precedence)
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Postfix_fixity { constant; precedence; location } ->
      json_of_variant ~name:"Signature.Pragma.Postfix_fixity"
        ~data:
          [ ("constant", json_of_qualified_identifier constant)
          ; ("precedence", json_of_option json_of_int precedence)
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Not { location } ->
      json_of_variant ~name:"Signature.Pragma.Not"
        ~data:[ ("location", json_of_location location) ]
  | Signature.Pragma.Open_module { module_identifier; location } ->
      json_of_variant ~name:"Signature.Pragma.Open_module"
        ~data:
          [ ( "module_identifier"
            , json_of_qualified_identifier module_identifier )
          ; ("location", json_of_location location)
          ]
  | Signature.Pragma.Abbreviation
      { module_identifier; abbreviation; location } ->
      json_of_variant ~name:"Signature.Pragma.Abbreviation"
        ~data:
          [ ( "module_identifier"
            , json_of_qualified_identifier module_identifier )
          ; ("abbreviation", json_of_identifier abbreviation)
          ; ("location", json_of_location location)
          ]

and json_of_signature_global_pragma global_pragma =
  match global_pragma with
  | Signature.Global_pragma.No_strengthening { location } ->
      json_of_variant ~name:"Signature.Global_pragma.No_strengthening"
        ~data:[ ("location", json_of_location location) ]
  | Signature.Global_pragma.Warn_on_coverage_error { location } ->
      json_of_variant ~name:"Signature.Global_pragma.Warn_on_coverage_error"
        ~data:[ ("location", json_of_location location) ]
  | Signature.Global_pragma.Raise_error_on_coverage_error { location } ->
      json_of_variant
        ~name:"Signature.Global_pragma.Raise_error_on_coverage_error"
        ~data:[ ("location", json_of_location location) ]

and json_of_signature_totality_declaration totality_declaration =
  match totality_declaration with
  | Signature.Totality.Declaration.Trust { location } ->
      json_of_variant ~name:"Signature.Totality.Declaration.Trust"
        ~data:[ ("location", json_of_location location) ]
  | Signature.Totality.Declaration.Numeric { order; location } ->
      json_of_variant ~name:"Signature.Totality.Declaration.Numeric"
        ~data:
          [ ( "order"
            , json_of_option json_of_signature_numeric_totality_order order
            )
          ; ("location", json_of_location location)
          ]
  | Signature.Totality.Declaration.Named
      { order; program; argument_labels; location } ->
      json_of_variant ~name:"Signature.Totality.Declaration.Named"
        ~data:
          [ ( "order"
            , json_of_option json_of_signature_named_totality_order order )
          ; ("program", json_of_identifier program)
          ; ( "argument_labels"
            , json_of_list json_of_identifier_opt argument_labels )
          ; ("location", json_of_location location)
          ]

and json_of_signature_numeric_totality_order totality_order =
  match totality_order with
  | Signature.Totality.Order.Argument { argument; location } ->
      json_of_variant ~name:"Signature.Order.Argument"
        ~data:
          [ ("argument", json_of_int argument)
          ; ("location", json_of_location location)
          ]
  | Signature.Totality.Order.Lexical_ordering { arguments; location } ->
      json_of_variant ~name:"Signature.Totality.Order.Lexical_ordering"
        ~data:
          [ ( "arguments"
            , json_of_list1 json_of_signature_numeric_totality_order
                arguments )
          ; ("location", json_of_location location)
          ]
  | Signature.Totality.Order.Simultaneous_ordering { arguments; location } ->
      json_of_variant ~name:"Signature.Totality.Order.Simultaneous_ordering"
        ~data:
          [ ( "arguments"
            , json_of_list1 json_of_signature_numeric_totality_order
                arguments )
          ; ("location", json_of_location location)
          ]

and json_of_signature_named_totality_order totality_order =
  match totality_order with
  | Signature.Totality.Order.Argument { argument; location } ->
      json_of_variant ~name:"Signature.Order.Argument"
        ~data:
          [ ("argument", json_of_identifier argument)
          ; ("location", json_of_location location)
          ]
  | Signature.Totality.Order.Lexical_ordering { arguments; location } ->
      json_of_variant ~name:"Signature.Totality.Order.Lexical_ordering"
        ~data:
          [ ( "arguments"
            , json_of_list1 json_of_signature_named_totality_order arguments
            )
          ; ("location", json_of_location location)
          ]
  | Signature.Totality.Order.Simultaneous_ordering { arguments; location } ->
      json_of_variant ~name:"Signature.Totality.Order.Simultaneous_ordering"
        ~data:
          [ ( "arguments"
            , json_of_list1 json_of_signature_named_totality_order arguments
            )
          ; ("location", json_of_location location)
          ]

and json_of_signature_declaration declaration =
  match declaration with
  | Signature.Declaration.Typ { identifier; kind; location } ->
      json_of_variant ~name:"Signature.Declaration.Typ"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("kind", json_of_lf_kind kind)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Const { identifier; typ; location } ->
      json_of_variant ~name:"Signature.Declaration.Const"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("typ", json_of_lf_typ typ)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.CompTyp
      { identifier; kind; datatype_flavour; location } ->
      json_of_variant ~name:"Signature.Declaration.CompTyp"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("kind", json_of_comp_kind kind)
          ; ( "datatype_flavour"
            , match datatype_flavour with
              | `Inductive -> json_of_string "inductive"
              | `Stratified -> json_of_string "stratified" )
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.CompCotyp { identifier; kind; location } ->
      json_of_variant ~name:"Signature.Declaration.CompCotyp"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("kind", json_of_comp_kind kind)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.CompConst { identifier; typ; location } ->
      json_of_variant ~name:"Signature.Declaration.CompConst"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("typ", json_of_comp_typ typ)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.CompDest
      { identifier; observation_type; return_type; location } ->
      json_of_variant ~name:"Signature.Declaration.CompDest"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("observation_type", json_of_comp_typ observation_type)
          ; ("return_type", json_of_comp_typ return_type)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; location }
    ->
      json_of_variant ~name:"Signature.Declaration.CompTypAbbrev"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("kind", json_of_comp_kind kind)
          ; ("typ", json_of_comp_typ typ)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Schema { identifier; schema; location } ->
      json_of_variant ~name:"Signature.Declaration.Schema"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("schema", json_of_schema schema)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Theorem { location; identifier; typ; order; body }
    ->
      json_of_variant ~name:"Signature.Declaration.Theorem"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("typ", json_of_comp_typ typ)
          ; ( "order"
            , json_of_option json_of_signature_totality_declaration order )
          ; ("body", json_of_comp_expression body)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Proof { location; identifier; typ; order; body } ->
      json_of_variant ~name:"Signature.Declaration.Proof"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("typ", json_of_comp_typ typ)
          ; ( "order"
            , json_of_option json_of_signature_totality_declaration order )
          ; ("body", json_of_harpoon_proof body)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Recursive_declarations { declarations; location }
    ->
      json_of_variant ~name:"Signature.Declaration.Recursive_declarations"
        ~data:
          [ ( "declarations"
            , json_of_list1 json_of_signature_declaration declarations )
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Val { identifier; typ; expression; location } ->
      json_of_variant ~name:"Signature.Declaration.Val"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("typ", json_of_option json_of_comp_typ typ)
          ; ("expression", json_of_comp_expression expression)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Query
      { identifier
      ; meta_context
      ; typ
      ; expected_solutions
      ; maximum_tries
      ; location
      } ->
      json_of_variant ~name:"Signature.Declaration.Query"
        ~data:
          [ ("identifier", json_of_option json_of_identifier identifier)
          ; ("meta_context", json_of_meta_context meta_context)
          ; ("typ", json_of_lf_typ typ)
          ; ( "expected_solutions"
            , json_of_option json_of_int expected_solutions )
          ; ("maximum_tries", json_of_option json_of_int maximum_tries)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.MQuery
      { identifier
      ; typ
      ; expected_solutions
      ; search_tries
      ; search_depth
      ; location
      } ->
      json_of_variant ~name:"Signature.Declaration.MQuery"
        ~data:
          [ ("identifier", json_of_option json_of_identifier identifier)
          ; ("typ", json_of_comp_typ typ)
          ; ( "expected_solutions"
            , json_of_option json_of_int expected_solutions )
          ; ("search_tries", json_of_option json_of_int search_tries)
          ; ("search_depth", json_of_option json_of_int search_depth)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Module { identifier; entries; location } ->
      json_of_variant ~name:"Signature.Declaration.Module"
        ~data:
          [ ("identifier", json_of_identifier identifier)
          ; ("entries", json_of_list json_of_signature_entry entries)
          ; ("location", json_of_location location)
          ]
  | Signature.Declaration.Comment { content; location } ->
      json_of_variant ~name:"Signature.Declaration.Comment"
        ~data:
          [ ("content", json_of_string content)
          ; ("location", json_of_location location)
          ]

and json_of_signature_entry = function
  | Signature.Entry.Pragma pragma ->
      json_of_variant ~name:"Signature.Entry.Pragma"
        ~data:[ ("pragma", json_of_signature_pragma pragma) ]
  | Signature.Entry.Declaration declaration ->
      json_of_variant ~name:"Signature.Entry.Declaration"
        ~data:[ ("pragma", json_of_signature_declaration declaration) ]

and json_of_signature signature =
  json_of_variant ~name:"Signature"
    ~data:
      [ ("declarations", json_of_list json_of_signature_declaration signature)
      ]
