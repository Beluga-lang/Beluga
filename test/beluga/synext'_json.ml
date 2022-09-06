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
  open LF

  let rec of_kind kind =
    match kind with
    | Kind.Typ _ -> `List [ `String "LF.Kind.Typ"; `Assoc [] ]
    | Kind.Arrow { domain; range; _ } ->
      `List
        [ `String "LF.Kind.Arrow"
        ; `Assoc [ ("domain", of_typ domain); ("range", of_kind range) ]
        ]
    | Kind.Pi { parameter_identifier; parameter_type; body; _ } ->
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
    | Typ.Constant { identifier; quoted; _ } ->
      `List
        [ `String "LF.Typ.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | Typ.Application { applicand; arguments; _ } ->
      `List
        [ `String "LF.Typ.Application"
        ; `Assoc
            [ ("applicand", of_typ applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | Typ.Arrow { domain; range; orientation; _ } ->
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
    | Typ.Pi { parameter_identifier; parameter_type; body; _ } ->
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
    | Term.Variable { identifier; _ } ->
      `List
        [ `String "LF.Term.Variable"
        ; `Assoc [ ("identifier", of_identifier identifier) ]
        ]
    | Term.Constant { identifier; quoted; _ } ->
      `List
        [ `String "LF.Term.Constant"
        ; `Assoc
            [ ("identifier", of_qualified_identifier identifier)
            ; ("quoted", `Bool quoted)
            ]
        ]
    | Term.Application { applicand; arguments; _ } ->
      `List
        [ `String "LF.Term.Application"
        ; `Assoc
            [ ("applicand", of_term applicand)
            ; ("arguments", `List (List.map of_term arguments))
            ]
        ]
    | Term.Abstraction { parameter_identifier; parameter_type; body; _ } ->
      `List
        [ `String "LF.Term.Abstraction"
        ; `Assoc
            [ ("parameter_identifier", of_identifier_opt parameter_identifier)
            ; ("parameter_type", of_option of_typ parameter_type)
            ; ("body", of_term body)
            ]
        ]
    | Term.Wildcard _ -> `List [ `String "LF.Term.Wildcard"; `Assoc [] ]
    | Term.TypeAnnotated { term; typ; _ } ->
      `List
        [ `String "LF.Term.TypeAnnotated"
        ; `Assoc [ ("term", of_term term); ("typ", of_typ typ) ]
        ]
end
