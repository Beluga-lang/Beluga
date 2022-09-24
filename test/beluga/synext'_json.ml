open Support
open Beluga
open Synext'

let of_option v = Fun.(Option.map v >> Option.value ~default:`Null)

let of_identifier identifier = `String (Identifier.show identifier)

let of_qualified_identifier identifier =
  `String (QualifiedIdentifier.show identifier)

let of_identifier_opt = of_option of_identifier

let of_qualified_identifier_opt = of_option of_qualified_identifier

let of_location location =
  if Location.is_ghost location then `Null
  else
    `Assoc
      [ ("filename", `String (Location.filename location))
      ; ("start_offset", `Int (Location.start_offset location))
      ; ("start_bol", `Int (Location.start_bol location))
      ; ("start_line", `Int (Location.start_line location))
      ; ("stop_offset", `Int (Location.stop_offset location))
      ; ("stop_bol", `Int (Location.stop_bol location))
      ; ("stop_line", `Int (Location.stop_line location))
      ]

let of_plicity plicity =
  match plicity with
  | Plicity.Explicit -> `String "explicit"
  | Plicity.Implicit -> `String "implicit"

let of_associativity associativity =
  match associativity with
  | Associativity.Left_associative -> "left-associative"
  | Associativity.Right_associative -> "right-associative"
  | Associativity.Non_associative -> "non-associative"

(** [without_locations json] is [json] without record fields named
    ["location"]. *)
let rec without_locations (json : Yojson.Safe.t) : Yojson.Safe.t =
  match json with
  | `Null | `Bool _ | `Intlit _ | `String _ | `Float _ | `Int _
  | `Variant (_, Option.None) -> json
  | `Tuple xs -> `Tuple (List.map without_locations xs)
  | `List xs -> `List (List.map without_locations xs)
  | `Assoc xs ->
    `Assoc
      (List.filter_map
         (fun (field, data) ->
           if String.(field = "location") then Option.none
           else Option.some (field, without_locations data))
         xs)
  | `Variant (l, Option.Some x) ->
    `Variant (l, Option.some (without_locations x))

module LF : sig
  open LF

  val of_kind : Kind.t -> Yojson.Safe.t

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_term : Term.t -> Yojson.Safe.t
end = struct
  let rec of_kind kind =
    match kind with
    | LF.Kind.Typ _ -> `List [ `String "LF.Kind.Typ" ]
    | LF.Kind.Arrow { domain; range; location } ->
      `List
        [ `String "LF.Kind.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_kind range)
            ; ("location", of_location location)
            ]
        ]
    | LF.Kind.Pi { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "LF.Kind.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_kind body)
            ; ("location", of_location location)
            ]
        ]

  and of_typ typ =
    match typ with
    | LF.Typ.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "LF.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | LF.Typ.Application { applicand; arguments; location } ->
      `List
        [ `String "LF.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ; ("location", of_location location)
            ]
        ]
    | LF.Typ.Arrow { domain; range; orientation; location } ->
      `List
        [ `String "LF.Typ.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_typ range)
            ; ( "orientation"
              , match orientation with
                | `Forward -> `String "forward"
                | `Backward -> `String "backward" )
            ; ("location", of_location location)
            ]
        ]
    | LF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "LF.Typ.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_typ body)
            ; ("location", of_location location)
            ]
        ]

  and of_term term =
    match term with
    | LF.Term.Variable { identifier; location } ->
      `List
        [ `String "LF.Term.Variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | LF.Term.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "LF.Term.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | LF.Term.Application { applicand; arguments; location } ->
      `List
        [ `String "LF.Term.Application"
        ; `Assoc
            [ ("applicand", of_term applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ; ("location", of_location location)
            ]
        ]
    | LF.Term.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "LF.Term.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term body)
            ; ("location", of_location location)
            ]
        ]
    | LF.Term.Wildcard { location } ->
      `List
        [ `String "LF.Term.Wildcard"
        ; `Assoc [ ("location", of_location location) ]
        ]
    | LF.Term.TypeAnnotated { term; typ; location } ->
      `List
        [ `String "LF.Term.TypeAnnotated"
        ; `Assoc
            [ ("term", of_term term)
            ; ("typ", of_typ typ)
            ; ("location", of_location location)
            ]
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
    | CLF.Typ.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "CLF.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Typ.Application { applicand; arguments; location } ->
      `List
        [ `String "CLF.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ; ("location", of_location location)
            ]
        ]
    | CLF.Typ.Arrow { domain; range; orientation; location } ->
      `List
        [ `String "CLF.Typ.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_typ range)
            ; ( "orientation"
              , match orientation with
                | `Forward -> `String "forward"
                | `Backward -> `String "backward" )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "CLF.Typ.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_typ parameter_type)
            ; ("body", of_typ body)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Typ.Block { elements; location } ->
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
            ; ("location", of_location location)
            ]
        ]

  and of_term term =
    match term with
    | CLF.Term.Variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Parameter_variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Parameter_variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Substitution_variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Substitution_variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "CLF.Term.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Application { applicand; arguments; location } ->
      `List
        [ `String "CLF.Term.Application"
        ; `Assoc
            [ ("applicand", of_term applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "CLF.Term.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term body)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.TypeAnnotated { term; typ; location } ->
      `List
        [ `String "CLF.Term.TypeAnnotated"
        ; `Assoc
            [ ("term", of_term term)
            ; ("typ", of_typ typ)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Hole { variant; location } ->
      `List
        [ `String "CLF.Term.Hole"
        ; `Assoc
            [ ( "variant"
              , match variant with
                | `Underscore -> `String "underscore"
                | `Unlabelled -> `String "unlabelled"
                | `Labelled label ->
                  `Assoc [ ("label", of_identifier label) ] )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Tuple { terms; location } ->
      `List
        [ `String "CLF.Term.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (terms |> List1.map of_term |> List1.to_list) )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Projection { term; projection; location } ->
      `List
        [ `String "CLF.Term.Projection"
        ; `Assoc
            [ ("term", of_term term)
            ; ( "projection"
              , match projection with
                | `By_identifier identifier -> of_identifier identifier
                | `By_position index -> `Int index )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Substitution { term; substitution; location } ->
      `List
        [ `String "CLF.Term.Substitution"
        ; `Assoc
            [ ("term", of_term term)
            ; ("substitution", of_substitution substitution)
            ; ("location", of_location location)
            ]
        ]

  and of_term_pattern term_pattern =
    match term_pattern with
    | CLF.Term.Pattern.Variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Pattern.Variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Parameter_variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Pattern.Parameter_variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Substitution_variable { identifier; location } ->
      `List
        [ `String "CLF.Term.Pattern.Substitution_variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Constant
        { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "CLF.Term.Pattern.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Application { applicand; arguments; location } ->
      `List
        [ `String "CLF.Term.Pattern.Application"
        ; `Assoc
            [ ("applicand", of_term_pattern applicand)
            ; ("arguments", `List (List.map of_term_pattern arguments))
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      `List
        [ `String "CLF.Term.Pattern.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term_pattern body)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.TypeAnnotated { term; typ; location } ->
      `List
        [ `String "CLF.Term.Pattern.TypeAnnotated"
        ; `Assoc
            [ ("term", of_term_pattern term)
            ; ("typ", of_typ typ)
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Wildcard { location } ->
      `List
        [ `String "CLF.Term.Pattern.Wildcard"
        ; `Assoc [ ("location", of_location location) ]
        ]
    | CLF.Term.Pattern.Tuple { terms; location } ->
      `List
        [ `String "CLF.Term.Pattern.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (terms |> List1.map of_term_pattern |> List1.to_list)
              )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Projection { term; projection; location } ->
      `List
        [ `String "CLF.Term.Pattern.Projection"
        ; `Assoc
            [ ("term", of_term_pattern term)
            ; ( "projection"
              , match projection with
                | `By_identifier identifier -> of_identifier identifier
                | `By_position index -> `Int index )
            ; ("location", of_location location)
            ]
        ]
    | CLF.Term.Pattern.Substitution { term; substitution; location } ->
      `List
        [ `String "CLF.Term.Pattern.Substitution"
        ; `Assoc
            [ ("term", of_term_pattern term)
            ; ("substitution", of_substitution substitution)
            ; ("location", of_location location)
            ]
        ]

  and of_substitution substition =
    match substition with
    | { CLF.Substitution.head; terms; location } ->
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
            ; ("location", of_location location)
            ]
        ]

  and of_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head; terms; location } ->
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
            ; ("location", of_location location)
            ]
        ]

  and of_context context =
    match context with
    | { CLF.Context.head; typings; location } ->
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
            ; ("location", of_location location)
            ]
        ]

  and of_context_pattern context_pattern =
    match context_pattern with
    | { CLF.Context.Pattern.head; typings; location } ->
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
            ; ("location", of_location location)
            ]
        ]
end

module Meta : sig
  open Meta

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_object : Object.t -> Yojson.Safe.t

  val of_pattern : Pattern.t -> Yojson.Safe.t

  val of_substitution : Substitution.t -> Yojson.Safe.t

  val of_context : Context.t -> Yojson.Safe.t

  val of_schema : Schema.t -> Yojson.Safe.t
end = struct
  let rec of_typ typ =
    match typ with
    | Meta.Typ.Context_schema { schema; location } ->
      `List
        [ `String "Meta.Typ.Context_schema"
        ; `Assoc
            [ ("schema", of_schema schema)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Typ.Contextual_typ { context; typ; location } ->
      `List
        [ `String "Meta.Typ.Contextual_typ"
        ; `Assoc
            [ ("context", CLF.of_context context)
            ; ("typ", CLF.of_typ typ)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Typ.Plain_substitution_typ { domain; range; location } ->
      `List
        [ `String "Meta.Typ.Plain_substitution_typ"
        ; `Assoc
            [ ("domain", CLF.of_context domain)
            ; ("range", CLF.of_context range)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Typ.Renaming_substitution_typ { domain; range; location } ->
      `List
        [ `String "Meta.Typ.Renaming_substitution_typ"
        ; `Assoc
            [ ("domain", CLF.of_context domain)
            ; ("range", CLF.of_context range)
            ; ("location", of_location location)
            ]
        ]

  and of_object object_ =
    match object_ with
    | Meta.Object.Context { context; location } ->
      `List
        [ `String "Meta.Object.Context"
        ; `Assoc
            [ ("context", CLF.of_context context)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Object.Contextual_term { context; term; location } ->
      `List
        [ `String "Meta.Object.Contextual_term"
        ; `Assoc
            [ ("context", CLF.of_context context)
            ; ("term", CLF.of_term term)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Object.Plain_substitution { domain; range; location } ->
      `List
        [ `String "Meta.Object.Plain_substitution"
        ; `Assoc
            [ ("domain", CLF.of_context domain)
            ; ("range", CLF.of_substitution range)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Object.Renaming_substitution { domain; range; location } ->
      `List
        [ `String "Meta.Object.Renaming_substitution"
        ; `Assoc
            [ ("domain", CLF.of_context domain)
            ; ("range", CLF.of_substitution range)
            ; ("location", of_location location)
            ]
        ]

  and of_pattern pattern =
    match pattern with
    | Meta.Pattern.Context { context; location } ->
      `List
        [ `String "Meta.Pattern.Context"
        ; `Assoc
            [ ("context", CLF.of_context_pattern context)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Pattern.Contextual_term { context; term; location } ->
      `List
        [ `String "Meta.Pattern.Contextual_term"
        ; `Assoc
            [ ("context", CLF.of_context_pattern context)
            ; ("term", CLF.of_term_pattern term)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Pattern.Plain_substitution { domain; range; location } ->
      `List
        [ `String "Meta.Pattern.Plain_substitution"
        ; `Assoc
            [ ("domain", CLF.of_context_pattern domain)
            ; ("range", CLF.of_substitution_pattern range)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Pattern.Renaming_substitution { domain; range; location } ->
      `List
        [ `String "Meta.Pattern.Renaming_substitution"
        ; `Assoc
            [ ("domain", CLF.of_context_pattern domain)
            ; ("range", CLF.of_substitution_pattern range)
            ; ("location", of_location location)
            ]
        ]

  and of_substitution substitution =
    match substitution with
    | { Meta.Substitution.objects; location } ->
      `List
        [ `String "Meta.Substitution"
        ; `Assoc
            [ ("objects", `List (List.map of_object objects))
            ; ("location", of_location location)
            ]
        ]

  and of_context context =
    match context with
    | { Meta.Context.bindings; location } ->
      `List
        [ `String "Meta.Context"
        ; `Assoc
            [ ( "bindings"
              , `List
                  (List.map
                     (fun (identifier, typ) ->
                       `Assoc
                         [ ("identifier", of_identifier identifier)
                         ; ("typ", of_typ typ)
                         ])
                     bindings) )
            ; ("location", of_location location)
            ]
        ]

  and of_schema schema =
    match schema with
    | Meta.Schema.Constant { identifier; location } ->
      `List
        [ `String "Meta.Schema.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | Meta.Schema.Alternation { schemas; location } ->
      `List
        [ `String "Meta.Schema.Alternation"
        ; `Assoc
            [ ( "schemas"
              , `List (schemas |> List2.map of_schema |> List2.to_list) )
            ; ("location", of_location location)
            ]
        ]
    | Meta.Schema.Element { some; block; location } ->
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
            ; ("location", of_location location)
            ]
        ]
end

module Comp : sig
  open Comp

  val of_kind : Kind.t -> Yojson.Safe.t

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_expression : Expression.t -> Yojson.Safe.t

  val of_pattern : Pattern.t -> Yojson.Safe.t

  val of_context : Context.t -> Yojson.Safe.t

  val of_totality_declaration : Totality.Declaration.t -> Yojson.Safe.t

  val of_numeric_totality_order : Int.t Totality.Order.t -> Yojson.Safe.t

  val of_named_totality_order :
    Identifier.t Totality.Order.t -> Yojson.Safe.t
end = struct
  let rec of_kind kind =
    match kind with
    | Comp.Kind.Ctype { location } ->
      `List
        [ `String "Comp.Kind.Ctype"
        ; `Assoc [ ("location", of_location location) ]
        ]
    | Comp.Kind.Arrow { domain; range; location } ->
      `List
        [ `String "Comp.Kind.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_kind range)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Kind.Pi
        { parameter_identifier; plicity; parameter_type; body; location } ->
      `List
        [ `String "Comp.Kind.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("plicity", of_plicity plicity)
            ; ("parameter_type", Meta.of_typ parameter_type)
            ; ("body", of_kind body)
            ; ("location", of_location location)
            ]
        ]

  and of_typ typ =
    match typ with
    | Comp.Typ.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "Comp.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Pi
        { parameter_identifier; plicity; parameter_type; body; location } ->
      `List
        [ `String "Comp.Typ.Pi"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("plicity", of_plicity plicity)
            ; ("parameter_type", Meta.of_typ parameter_type)
            ; ("body", of_typ body)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Arrow { domain; range; location } ->
      `List
        [ `String "Comp.Typ.Arrow"
        ; `Assoc
            [ ("domain", of_typ domain)
            ; ("range", of_typ range)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Cross { typs; location } ->
      `List
        [ `String "Comp.Typ.Cross"
        ; `Assoc
            [ ("typs", `List (typs |> List2.to_list |> List.map of_typ))
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Box { meta_type; location } ->
      `List
        [ `String "Comp.Typ.Box"
        ; `Assoc
            [ ("meta_type", Meta.of_typ meta_type)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Application { applicand; arguments; location } ->
      `List
        [ `String "Comp.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ( "arguments"
              , `List (arguments |> List1.to_list |> List.map of_typ) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Base { applicand; arguments; location; _ } ->
      `List
        [ `String "Comp.Typ.Base"
        ; `Assoc
            [ ("applicand", of_qualified_identifier applicand)
            ; ("arguments", `List (List.map Meta.of_object arguments))
            ; ("location", of_location location)
            ]
        ]
    | Comp.Typ.Cobase { applicand; arguments; location; _ } ->
      `List
        [ `String "Comp.Typ.Cobase"
        ; `Assoc
            [ ("applicand", of_qualified_identifier applicand)
            ; ("arguments", `List (List.map Meta.of_object arguments))
            ; ("location", of_location location)
            ]
        ]

  and of_expression expression =
    match expression with
    | Comp.Expression.Variable { identifier; location } ->
      `List
        [ `String "Comp.Expression.Variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Constant { identifier; quoted; location; operator = _ }
      ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "Comp.Expression.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Fn { parameters; body; location } ->
      `List
        [ `String "Comp.Expression.Fn"
        ; `Assoc
            [ ( "parameters"
              , `List
                  (parameters |> List1.to_list |> List.map of_identifier_opt)
              )
            ; ("body", of_expression body)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Mlam { parameters; body; location } ->
      `List
        [ `String "Comp.Expression.Mlam"
        ; `Assoc
            [ ( "parameters"
              , `List
                  (parameters |> List1.to_list
                  |> List.map Fun.(Pair.fst >> of_identifier_opt)) )
            ; ("body", of_expression body)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Fun { branches; location } ->
      `List
        [ `String "Comp.Expression.Fun"
        ; `Assoc
            [ ( "branchs"
              , `List
                  (branches |> List1.to_list
                  |> List.map (fun (patterns, body) ->
                         `Assoc
                           [ ( "patterns"
                             , `List
                                 (patterns |> List1.to_list
                                |> List.map of_pattern) )
                           ; ("body", of_expression body)
                           ])) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Let { pattern; scrutinee; body; location } ->
      `List
        [ `String "Comp.Expression.Let"
        ; `Assoc
            [ ("pattern", of_pattern pattern)
            ; ("scrutinee", of_expression scrutinee)
            ; ("body", of_expression body)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Box { meta_object; location } ->
      `List
        [ `String "Comp.Expression.Box"
        ; `Assoc
            [ ("meta_object", Meta.of_object meta_object)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Impossible { scrutinee; location } ->
      `List
        [ `String "Comp.Expression.Impossible"
        ; `Assoc
            [ ("scrutinee", of_expression scrutinee)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Case { scrutinee; check_coverage; branches; location }
      ->
      `List
        [ `String "Comp.Expression.Case"
        ; `Assoc
            [ ("scrutinee", of_expression scrutinee)
            ; ("check_coverage", `Bool check_coverage)
            ; ( "branches"
              , `List
                  (branches |> List1.to_list
                  |> List.map (fun (pattern, body) ->
                         `Assoc
                           [ ("pattern", of_pattern pattern)
                           ; ("body", of_expression body)
                           ])) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Tuple { elements; location } ->
      `List
        [ `String "Comp.Expression.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (elements |> List2.to_list |> List.map of_expression)
              )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Hole { label; location } ->
      `List
        [ `String "Comp.Expression.Hole"
        ; `Assoc
            [ ("label", of_identifier_opt label)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.BoxHole { location } ->
      `List
        [ `String "Comp.Expression.BoxHole"
        ; `Assoc [ ("location", of_location location) ]
        ]
    | Comp.Expression.Application { applicand; arguments; location } ->
      `List
        [ `String "Comp.Expression.Application"
        ; `Assoc
            [ ("applicand", of_expression applicand)
            ; ( "arguments"
              , `List (arguments |> List1.to_list |> List.map of_expression)
              )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.Observation { observation; arguments; location } ->
      `List
        [ `String "Comp.Expression.Observation"
        ; `Assoc
            [ ("observation", of_qualified_identifier observation)
            ; ("arguments", `List (List.map of_expression arguments))
            ; ("location", of_location location)
            ]
        ]
    | Comp.Expression.TypeAnnotated { expression; typ; location } ->
      `List
        [ `String "Comp.Expression.TypeAnnotated"
        ; `Assoc
            [ ("expression", of_expression expression)
            ; ("typ", of_typ typ)
            ; ("location", of_location location)
            ]
        ]

  and of_pattern pattern =
    match pattern with
    | Comp.Pattern.Variable { identifier; location } ->
      `List
        [ `String "Comp.Pattern.Variable"
        ; `Assoc
            [ ("identifier", of_identifier identifier)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      `List
        [ `String "Comp.Pattern.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.MetaObject { meta_object; location } ->
      `List
        [ `String "Comp.Pattern.MetaObject"
        ; `Assoc
            [ ("meta_object", Meta.of_pattern meta_object)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.Tuple { elements; location } ->
      `List
        [ `String "Comp.Pattern.Tuple"
        ; `Assoc
            [ ( "elements"
              , `List (elements |> List2.to_list |> List.map of_pattern) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.Application { applicand; arguments; location } ->
      `List
        [ `String "Comp.Pattern.Application"
        ; `Assoc
            [ ("applicand", of_pattern applicand)
            ; ( "arguments"
              , `List (arguments |> List1.to_list |> List.map of_pattern) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.Observation { observation; arguments; location } ->
      `List
        [ `String "Comp.Pattern.Observation"
        ; `Assoc
            [ ("observation", of_qualified_identifier observation)
            ; ("arguments", `List (List.map of_pattern arguments))
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.TypeAnnotated { pattern; typ; location } ->
      `List
        [ `String "Comp.Pattern.TypeAnnotated"
        ; `Assoc
            [ ("pattern", of_pattern pattern)
            ; ("typ", of_typ typ)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; location } ->
      `List
        [ `String "Comp.Pattern.MetaTypeAnnotated"
        ; `Assoc
            [ ( "annotation_identifier"
              , of_identifier_opt annotation_identifier )
            ; ("annotation_type", Meta.of_typ annotation_type)
            ; ("body", of_pattern body)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Pattern.Wildcard { location } ->
      `List
        [ `String "Comp.Pattern.Wildcard"
        ; `Assoc [ ("location", of_location location) ]
        ]

  and of_context context =
    match context with
    | { Comp.Context.bindings; location } ->
      `List
        [ `String "Comp.Context"
        ; `Assoc
            [ ( "bindings"
              , `List
                  (List.map
                     (fun (identifier, typ) ->
                       `Assoc
                         [ ("identifier", of_identifier identifier)
                         ; ("typ", of_typ typ)
                         ])
                     bindings) )
            ; ("location", of_location location)
            ]
        ]

  and of_totality_declaration totality_declaration =
    match totality_declaration with
    | Comp.Totality.Declaration.Trust { location } ->
      `List
        [ `String "Comp.Totality.Declaration.Trust"
        ; `Assoc [ ("location", of_location location) ]
        ]
    | Comp.Totality.Declaration.Numeric { order; location } ->
      `List
        [ `String "Comp.Totality.Declaration.Numeric"
        ; `Assoc
            [ ("order", of_option of_numeric_totality_order order)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Totality.Declaration.Named
        { order; program; argument_labels; location } ->
      `List
        [ `String "Comp.Totality.Declaration.Named"
        ; `Assoc
            [ ("order", of_option of_named_totality_order order)
            ; ("program", of_identifier program)
            ; ( "argument_labels"
              , `List (List.map of_identifier_opt argument_labels) )
            ; ("location", of_location location)
            ]
        ]

  and of_numeric_totality_order totality_order =
    match totality_order with
    | Comp.Totality.Order.Argument { argument; location } ->
      `List
        [ `String "Comp.Order.Argument"
        ; `Assoc
            [ ("argument", `Int argument)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Totality.Order.Lexical_ordering { arguments; location } ->
      `List
        [ `String "Comp.Totality.Order.Lexical_ordering"
        ; `Assoc
            [ ( "arguments"
              , `List
                  (arguments |> List1.to_list
                  |> List.map of_numeric_totality_order) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Totality.Order.Simultaneous_ordering { arguments; location } ->
      `List
        [ `String "Comp.Totality.Order.Simultaneous_ordering"
        ; `Assoc
            [ ( "arguments"
              , `List
                  (arguments |> List1.to_list
                  |> List.map of_numeric_totality_order) )
            ; ("location", of_location location)
            ]
        ]

  and of_named_totality_order totality_order =
    match totality_order with
    | Comp.Totality.Order.Argument { argument; location } ->
      `List
        [ `String "Comp.Order.Argument"
        ; `Assoc
            [ ("argument", of_identifier argument)
            ; ("location", of_location location)
            ]
        ]
    | Comp.Totality.Order.Lexical_ordering { arguments; location } ->
      `List
        [ `String "Comp.Totality.Order.Lexical_ordering"
        ; `Assoc
            [ ( "arguments"
              , `List
                  (arguments |> List1.to_list
                  |> List.map of_named_totality_order) )
            ; ("location", of_location location)
            ]
        ]
    | Comp.Totality.Order.Simultaneous_ordering { arguments; location } ->
      `List
        [ `String "Comp.Totality.Order.Simultaneous_ordering"
        ; `Assoc
            [ ( "arguments"
              , `List
                  (arguments |> List1.to_list
                  |> List.map of_named_totality_order) )
            ; ("location", of_location location)
            ]
        ]
end
