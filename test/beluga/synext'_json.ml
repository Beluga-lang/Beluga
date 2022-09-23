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
    | LF.Typ.Constant { identifier; quoted; location; operator = _ }
    (* Don't serialize [operator] since it is resolved from the signature. *)
      ->
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
    | LF.Term.Constant { identifier; quoted; location; operator = _ }
    (* Don't serialize [operator] since it is resolved from the signature. *)
      ->
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
    | CLF.Typ.Constant { identifier; quoted; location; operator = _ }
    (* Don't serialize [operator] since it is resolved from the signature. *)
      ->
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
    | CLF.Term.Constant { identifier; quoted; location; operator = _ }
    (* Don't serialize [operator] since it is resolved from the signature. *)
      ->
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
        { identifier; quoted; location; operator = _ }
    (* Don't serialize [operator] since it is resolved from the signature. *)
      ->
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

  val of_schema : Schema.t -> Yojson.Safe.t
end = struct
  let rec of_schema schema =
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
