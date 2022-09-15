open Support
open Beluga
open Synext'

let of_option v = Fun.(Option.map v >> Option.value ~default:`Null)

let of_identifier identifier = `String (Identifier.show identifier)

let of_qualified_identifier identifier =
  `String (QualifiedIdentifier.show identifier)

let of_identifier_opt = of_option of_identifier

let of_qualified_identifier_opt = of_option of_qualified_identifier

module LF : sig
  open LF

  val of_kind : Kind.t -> Yojson.Safe.t

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_term : Term.t -> Yojson.Safe.t
end = struct
  let rec of_kind kind =
    match kind with
    | LF.Kind.Typ _ -> `List [ `String "LF.Kind.Typ" ]
    | LF.Kind.Arrow { domain; range; _ } ->
      `List
        [ `String "LF.Kind.Arrow"
        ; `Assoc [ ("domain", of_typ domain); ("range", of_kind range) ]
        ]
    | LF.Kind.Pi { parameter_identifier; parameter_type; body; _ } ->
      `List
        [ `String "LF.Kind.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_kind body)
            ]
        ]

  and of_typ typ =
    match typ with
    | LF.Typ.Constant { identifier; quoted; _ } ->
      `List
        [ `String "LF.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | LF.Typ.Application { applicand; arguments; _ } ->
      `List
        [ `String "LF.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | LF.Typ.Arrow { domain; range; orientation; _ } ->
      `List
        [ `String "LF.Typ.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_typ range)
            ; ( "orientation"
              , match orientation with
                | `Forward -> `String "forward"
                | `Backward -> `String "backward" )
            ]
        ]
    | LF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      `List
        [ `String "LF.Typ.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_typ body)
            ]
        ]

  and of_term term =
    match term with
    | LF.Term.Variable { identifier; _ } ->
      `List
        [ `String "LF.Term.Variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | LF.Term.Constant { identifier; quoted; _ } ->
      `List
        [ `String "LF.Term.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | LF.Term.Application { applicand; arguments; _ } ->
      `List
        [ `String "LF.Term.Application"
        ; `Assoc
            [ ("applicand", of_term applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | LF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
      `List
        [ `String "LF.Term.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term body)
            ]
        ]
    | LF.Term.Wildcard _ -> `List [ `String "LF.Term.Wildcard"; `Assoc [] ]
    | LF.Term.TypeAnnotated { term; typ; _ } ->
      `List
        [ `String "LF.Term.TypeAnnotated"
        ; `Assoc [ ("term", of_term term); ("typ", of_typ typ) ]
        ]
end

module CLF : sig
  open CLF

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_term : Term.t -> Yojson.Safe.t

  val of_term_pattern : Term.Pattern.t -> Yojson.Safe.t

  val of_substitution : Substitution.t -> Yojson.Safe.t

  val of_substitution_pattern : Substitution.Pattern.t -> Yojson.Safe.t

  val of_context : Context.t -> Yojson.Safe.t

  val of_context_pattern : Context.Pattern.t -> Yojson.Safe.t
end = struct
  let rec of_typ typ =
    match typ with
    | CLF.Typ.Constant { identifier; quoted; _ } ->
      `List
        [ `String "CLF.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | CLF.Typ.Application { applicand; arguments; _ } ->
      `List
        [ `String "CLF.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | CLF.Typ.Arrow { domain; range; orientation; _ } ->
      `List
        [ `String "CLF.Typ.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_typ range)
            ; ( "orientation"
              , match orientation with
                | `Forward -> `String "forward"
                | `Backward -> `String "backward" )
            ]
        ]
    | CLF.Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
      `List
        [ `String "CLF.Typ.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_typ body)
            ]
        ]
    | CLF.Typ.Block { elements; _ } ->
      `List
        [ `String "CLF.Typ.Block"
        ; `Assoc
            [ ( "elements"
              , match elements with
                | `Unnamed typ -> of_typ typ
                | `Record typings ->
                  `List
                    (typings
                    |> List1.map (fun (identifier, typ) ->
                           `Assoc
                             [ ("identifier", of_identifier identifier)
                             ; ("typ", of_typ typ)
                             ])
                    |> List1.to_list) )
            ]
        ]

  and of_term term =
    match term with
    | CLF.Term.Variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Parameter_variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Parameter_variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Substitution_variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Substitution_variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Constant { identifier; quoted; _ } ->
      `List
        [ `String "CLF.Term.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | CLF.Term.Application { applicand; arguments; _ } ->
      `List
        [ `String "CLF.Term.Application"
        ; `Assoc
            [ ("applicand", of_term applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | CLF.Term.Abstraction { parameter_identifier; parameter_type; body; _ }
      ->
      `List
        [ `String "CLF.Term.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term body)
            ]
        ]
    | CLF.Term.TypeAnnotated { term; typ; _ } ->
      `List
        [ `String "CLF.Term.TypeAnnotated"
        ; `Assoc [ ("term", of_term term); ("typ", of_typ typ) ]
        ]
    | CLF.Term.Hole { variant; _ } ->
      `List
        [ `String "CLF.Term.Hole"
        ; `Assoc
            [ ( "variant"
              , match variant with
                | `Underscore -> `String "underscore"
                | `Unlabelled -> `String "unlabelled"
                | `Labelled label ->
                  `Assoc [ ("label", of_identifier label) ] )
            ]
        ]
    | CLF.Term.Tuple { terms; _ } ->
      `List
        [ `String "CLF.Term.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (terms |> List1.map of_term |> List1.to_list) )
            ]
        ]
    | CLF.Term.Projection { term; projection; _ } ->
      `List
        [ `String "CLF.Term.Projection"
        ; `Assoc
            [ ("term", of_term term)
            ; ( "projection"
              , match projection with
                | `By_identifier identifier -> of_identifier identifier
                | `By_position index -> `Int index )
            ]
        ]
    | CLF.Term.Substitution { term; substitution; _ } ->
      `List
        [ `String "CLF.Term.Substitution"
        ; `Assoc
            [ ("term", of_term term)
            ; ("substitution", of_substitution substitution)
            ]
        ]

  and of_term_pattern term_pattern =
    match term_pattern with
    | CLF.Term.Pattern.Variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Pattern.Parameter_variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Parameter_variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Pattern.Substitution_variable { identifier; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Substitution_variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | CLF.Term.Pattern.Constant { identifier; quoted; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | CLF.Term.Pattern.Application { applicand; arguments; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Application"
        ; `Assoc
            [ ("applicand", of_term_pattern applicand)
            ; ("arguments", `List (List.map of_term_pattern arguments))
            ]
        ]
    | CLF.Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term_pattern body)
            ]
        ]
    | CLF.Term.Pattern.TypeAnnotated { term; typ; _ } ->
      `List
        [ `String "CLF.Term.Pattern.TypeAnnotated"
        ; `Assoc [ ("term", of_term_pattern term); ("typ", of_typ typ) ]
        ]
    | CLF.Term.Pattern.Wildcard _ ->
      `List [ `String "CLF.Term.Pattern.Wildcard" ]
    | CLF.Term.Pattern.Tuple { terms; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (terms |> List1.map of_term_pattern |> List1.to_list)
              )
            ]
        ]
    | CLF.Term.Pattern.Projection { term; projection; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Projection"
        ; `Assoc
            [ ("term", of_term_pattern term)
            ; ( "projection"
              , match projection with
                | `By_identifier identifier -> of_identifier identifier
                | `By_position index -> `Int index )
            ]
        ]
    | CLF.Term.Pattern.Substitution { term; substitution; _ } ->
      `List
        [ `String "CLF.Term.Pattern.Substitution"
        ; `Assoc
            [ ("term", of_term_pattern term)
            ; ("substitution", of_substitution substitution)
            ]
        ]

  and of_substitution substition =
    match substition with
    | { CLF.Substitution.head; terms; _ } ->
      `List
        [ `String "CLF.Substitution"
        ; `Assoc
            [ ( "head"
              , match head with
                | CLF.Substitution.Head.None ->
                  `List [ `String "CLF.Substitution.Head.None" ]
                | CLF.Substitution.Head.Identity _ ->
                  `List [ `String "CLF.Substitution.Head.Identity" ]
                | CLF.Substitution.Head.Substitution_variable
                    { identifier; closure; _ } ->
                  `List
                    [ `String "CLF.Substitution.Head.Substitution_variable"
                    ; `Assoc
                        [ ("identifier", of_identifier identifier)
                        ; ("closure", of_option of_substitution closure)
                        ]
                    ] )
            ; ("terms", `List (List.map of_term terms))
            ]
        ]

  and of_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head; terms; _ } ->
      `List
        [ `String "CLF.Substitution"
        ; `Assoc
            [ ( "head"
              , match head with
                | CLF.Substitution.Pattern.Head.None ->
                  `List [ `String "CLF.Substitution.Pattern.Head.None" ]
                | CLF.Substitution.Pattern.Head.Identity _ ->
                  `List [ `String "CLF.Substitution.Pattern.Head.Identity" ]
                | CLF.Substitution.Pattern.Head.Substitution_variable
                    { identifier; closure; _ } ->
                  `List
                    [ `String
                        "CLF.Substitution.Pattern.Head.Substitution_variable"
                    ; `Assoc
                        [ ("identifier", of_identifier identifier)
                        ; ("closure", of_option of_substitution closure)
                        ]
                    ] )
            ; ("terms", `List (List.map of_term_pattern terms))
            ]
        ]

  and of_context context =
    match context with
    | { CLF.Context.head; typings; _ } ->
      `List
        [ `String "CLF.Context"
        ; `Assoc
            [ ( "head"
              , match head with
                | CLF.Context.Head.None ->
                  `List [ `String "CLF.Context.Head.None" ]
                | CLF.Context.Head.Hole _ ->
                  `List [ `String "CLF.Context.Head.Hole" ]
                | CLF.Context.Head.Context_variable { identifier; _ } ->
                  `List
                    [ `String "CLF.Context.Head.Context_variable"
                    ; `Assoc [ ("identifier", of_identifier identifier) ]
                    ] )
            ; ( "typings"
              , `List
                  (List.map
                     (fun (identifier, typ) ->
                       `Assoc
                         [ ("identifier", of_identifier identifier)
                         ; ("typ", of_typ typ)
                         ])
                     typings) )
            ]
        ]

  and of_context_pattern context_pattern =
    match context_pattern with
    | { CLF.Context.Pattern.head; typings; _ } ->
      `List
        [ `String "CLF.Context.Pattern"
        ; `Assoc
            [ ( "head"
              , match head with
                | CLF.Context.Pattern.Head.None ->
                  `List [ `String "CLF.Context.Head.Pattern.None" ]
                | CLF.Context.Pattern.Head.Hole _ ->
                  `List [ `String "CLF.Context.Head.Pattern.Hole" ]
                | CLF.Context.Pattern.Head.Context_variable { identifier; _ }
                  ->
                  `List
                    [ `String "CLF.Context.Pattern.Head.Context_variable"
                    ; `Assoc [ ("identifier", of_identifier identifier) ]
                    ] )
            ; ( "typings"
              , `List
                  (List.map
                     (fun (identifier, typ) ->
                       `Assoc
                         [ ("identifier", of_identifier identifier)
                         ; ("typ", of_typ typ)
                         ])
                     typings) )
            ]
        ]
end

module Meta : sig
  open Meta

  val of_schema : Schema.t -> Yojson.Safe.t
end = struct
  let rec of_schema schema =
    match schema with
    | Meta.Schema.Constant { identifier; _ } ->
      `List
        [ `String "Meta.Schema.Constant"
        ; `Assoc [ ("identifier", of_qualified_identifier identifier) ]
        ]
    | Meta.Schema.Alternation { schemas; _ } ->
      `List
        [ `String "Meta.Schema.Alternation"
        ; `Assoc
            [ ( "schemas"
              , `List (schemas |> List2.map of_schema |> List2.to_list) )
            ]
        ]
    | Meta.Schema.Element { some; block; _ } ->
      `List
        [ `String "Meta.Schema.Element"
        ; `Assoc
            [ ( "some"
              , of_option
                  (fun some ->
                    `List
                      (some
                      |> List1.map (fun (identifier, typ) ->
                             `Assoc
                               [ ("identifier", of_identifier identifier)
                               ; ("typ", CLF.of_typ typ)
                               ])
                      |> List1.to_list))
                  some )
            ; ( "block"
              , match block with
                | `Unnamed typ -> CLF.of_typ typ
                | `Record typings ->
                  `List
                    (typings
                    |> List1.map (fun (identifier, typ) ->
                           `Assoc
                             [ ("identifier", of_identifier identifier)
                             ; ("typ", CLF.of_typ typ)
                             ])
                    |> List1.to_list) )
            ]
        ]
end
