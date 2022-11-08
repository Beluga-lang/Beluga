(** JSON serialization for the external syntax.

    This is used to display parsed external syntax objects when parser tests
    fail. *)

open Support
open Beluga
open Synext'

let[@inline] of_association e = `Assoc e

let[@inline] of_int i = `Int i

let[@inline] of_bool b = `Bool b

let[@inline] of_string s = `String s

let[@inline] of_list f l = `List (List.map f l)

let[@inline] of_list1 f l = of_list f (List1.to_list l)

let[@inline] of_list2 f l = of_list f (List2.to_list l)

let[@inline] of_variant ~name ~data =
  `List [ of_string name; of_association data ]

let[@inline] of_option v = Fun.(Option.map v >> Option.value ~default:`Null)

let[@inline] of_identifier identifier =
  of_string (Identifier.show identifier)

let[@inline] of_qualified_identifier identifier =
  of_string (QualifiedIdentifier.show identifier)

let of_identifier_opt = of_option of_identifier

let of_qualified_identifier_opt = of_option of_qualified_identifier

let of_location =
  Fun.(
    Option.from_predicate Location.is_ghost
    >> of_option (fun location ->
           of_association
             [ ("filename", of_string (Location.filename location))
             ; ("start_offset", of_int (Location.start_offset location))
             ; ("start_bol", of_int (Location.start_bol location))
             ; ("start_line", of_int (Location.start_line location))
             ; ("stop_offset", of_int (Location.stop_offset location))
             ; ("stop_bol", of_int (Location.stop_bol location))
             ; ("stop_line", of_int (Location.stop_line location))
             ]))

let[@inline] of_plicity plicity =
  match plicity with
  | Plicity.Explicit -> of_string "explicit"
  | Plicity.Implicit -> of_string "implicit"

let[@inline] of_associativity associativity =
  match associativity with
  | Associativity.Left_associative -> of_string "left-associative"
  | Associativity.Right_associative -> of_string "right-associative"
  | Associativity.Non_associative -> of_string "non-associative"

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
    | LF.Kind.Typ { location } ->
      of_variant ~name:"LF.Kind.Typ"
        ~data:[ ("location", of_location location) ]
    | LF.Kind.Arrow { domain; range; location } ->
      of_variant ~name:"LF.Kind.Arrow"
        ~data:
          [ ("domain", of_typ domain)
          ; ("range", of_kind range)
          ; ("location", of_location location)
          ]
    | LF.Kind.Pi { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"LF.Kind.Pi"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_typ parameter_type)
          ; ("body", of_kind body)
          ; ("location", of_location location)
          ]

  and of_typ typ =
    match typ with
    | LF.Typ.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"LF.Typ.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | LF.Typ.Application { applicand; arguments; location } ->
      of_variant ~name:"LF.Typ.Application"
        ~data:
          [ ("applicand", of_typ applicand)
          ; ("arguments", of_list of_term arguments)
          ; ("location", of_location location)
          ]
    | LF.Typ.Arrow { domain; range; orientation; location } ->
      of_variant ~name:"LF.Typ.Arrow"
        ~data:
          [ ("domain", of_typ domain)
          ; ("range", of_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> of_string "forward"
              | `Backward -> of_string "backward" )
          ; ("location", of_location location)
          ]
    | LF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"LF.Typ.Pi"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_typ parameter_type)
          ; ("body", of_typ body)
          ; ("location", of_location location)
          ]

  and of_term term =
    match term with
    | LF.Term.Variable { identifier; location } ->
      of_variant ~name:"LF.Term.Variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | LF.Term.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"LF.Term.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | LF.Term.Application { applicand; arguments; location } ->
      of_variant ~name:"LF.Term.Application"
        ~data:
          [ ("applicand", of_term applicand)
          ; ("arguments", of_list of_term arguments)
          ; ("location", of_location location)
          ]
    | LF.Term.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"LF.Term.Abstraction"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_option of_typ parameter_type)
          ; ("body", of_term body)
          ; ("location", of_location location)
          ]
    | LF.Term.Wildcard { location } ->
      of_variant ~name:"LF.Term.Wildcard"
        ~data:[ ("location", of_location location) ]
    | LF.Term.TypeAnnotated { term; typ; location } ->
      of_variant ~name:"LF.Term.TypeAnnotated"
        ~data:
          [ ("term", of_term term)
          ; ("typ", of_typ typ)
          ; ("location", of_location location)
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
      of_variant ~name:"CLF.Typ.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | CLF.Typ.Application { applicand; arguments; location } ->
      of_variant ~name:"CLF.Typ.Application"
        ~data:
          [ ("applicand", of_typ applicand)
          ; ("arguments", of_list of_term arguments)
          ; ("location", of_location location)
          ]
    | CLF.Typ.Arrow { domain; range; orientation; location } ->
      of_variant ~name:"CLF.Typ.Arrow"
        ~data:
          [ ("domain", of_typ domain)
          ; ("range", of_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> of_string "forward"
              | `Backward -> of_string "backward" )
          ; ("location", of_location location)
          ]
    | CLF.Typ.Pi { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"CLF.Typ.Pi"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_typ parameter_type)
          ; ("body", of_typ body)
          ; ("location", of_location location)
          ]
    | CLF.Typ.Block { elements; location } ->
      of_variant ~name:"CLF.Typ.Block"
        ~data:
          [ ( "elements"
            , match elements with
              | `Unnamed typ -> of_typ typ
              | `Record bindings ->
                of_list1
                  (fun (identifier, typ) ->
                    of_association
                      [ ("identifier", of_identifier identifier)
                      ; ("typ", of_typ typ)
                      ])
                  bindings )
          ; ("location", of_location location)
          ]

  and of_term term =
    match term with
    | CLF.Term.Variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Parameter_variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Parameter_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Substitution_variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Substitution_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"CLF.Term.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | CLF.Term.Application { applicand; arguments; location } ->
      of_variant ~name:"CLF.Term.Application"
        ~data:
          [ ("applicand", of_term applicand)
          ; ("arguments", of_list of_term arguments)
          ; ("location", of_location location)
          ]
    | CLF.Term.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"CLF.Term.Abstraction"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_option of_typ parameter_type)
          ; ("body", of_term body)
          ; ("location", of_location location)
          ]
    | CLF.Term.TypeAnnotated { term; typ; location } ->
      of_variant ~name:"CLF.Term.TypeAnnotated"
        ~data:
          [ ("term", of_term term)
          ; ("typ", of_typ typ)
          ; ("location", of_location location)
          ]
    | CLF.Term.Hole { variant; location } ->
      of_variant ~name:"CLF.Term.Hole"
        ~data:
          [ ( "variant"
            , match variant with
              | `Underscore -> of_string "underscore"
              | `Unlabelled -> of_string "unlabelled"
              | `Labelled label ->
                of_association [ ("label", of_identifier label) ] )
          ; ("location", of_location location)
          ]
    | CLF.Term.Tuple { terms; location } ->
      of_variant ~name:"CLF.Term.Tuple"
        ~data:
          [ ("elements", of_list1 of_term terms)
          ; ("location", of_location location)
          ]
    | CLF.Term.Projection { term; projection; location } ->
      of_variant ~name:"CLF.Term.Projection"
        ~data:
          [ ("term", of_term term)
          ; ( "projection"
            , match projection with
              | `By_identifier identifier -> of_identifier identifier
              | `By_position index -> of_int index )
          ; ("location", of_location location)
          ]
    | CLF.Term.Substitution { term; substitution; location } ->
      of_variant ~name:"CLF.Term.Substitution"
        ~data:
          [ ("term", of_term term)
          ; ("substitution", of_substitution substitution)
          ; ("location", of_location location)
          ]

  and of_term_pattern term_pattern =
    match term_pattern with
    | CLF.Term.Pattern.Variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Pattern.Variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Parameter_variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Pattern.Parameter_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Substitution_variable { identifier; location } ->
      of_variant ~name:"CLF.Term.Pattern.Substitution_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Constant
        { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"CLF.Term.Pattern.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Application { applicand; arguments; location } ->
      of_variant ~name:"CLF.Term.Pattern.Application"
        ~data:
          [ ("applicand", of_term_pattern applicand)
          ; ("arguments", of_list of_term_pattern arguments)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Abstraction
        { parameter_identifier; parameter_type; body; location } ->
      of_variant ~name:"CLF.Term.Pattern.Abstraction"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("parameter_type", of_option of_typ parameter_type)
          ; ("body", of_term_pattern body)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.TypeAnnotated { term; typ; location } ->
      of_variant ~name:"CLF.Term.Pattern.TypeAnnotated"
        ~data:
          [ ("term", of_term_pattern term)
          ; ("typ", of_typ typ)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Wildcard { location } ->
      of_variant ~name:"CLF.Term.Pattern.Wildcard"
        ~data:[ ("location", of_location location) ]
    | CLF.Term.Pattern.Tuple { terms; location } ->
      of_variant ~name:"CLF.Term.Pattern.Tuple"
        ~data:
          [ ("elements", of_list1 of_term_pattern terms)
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Projection { term; projection; location } ->
      of_variant ~name:"CLF.Term.Pattern.Projection"
        ~data:
          [ ("term", of_term_pattern term)
          ; ( "projection"
            , match projection with
              | `By_identifier identifier -> of_identifier identifier
              | `By_position index -> of_int index )
          ; ("location", of_location location)
          ]
    | CLF.Term.Pattern.Substitution { term; substitution; location } ->
      of_variant ~name:"CLF.Term.Pattern.Substitution"
        ~data:
          [ ("term", of_term_pattern term)
          ; ("substitution", of_substitution substitution)
          ; ("location", of_location location)
          ]

  and of_substitution substition =
    match substition with
    | { CLF.Substitution.head; terms; location } ->
      of_variant ~name:"CLF.Substitution"
        ~data:
          [ ("head", of_substitution_head head)
          ; ("terms", of_list of_term terms)
          ; ("location", of_location location)
          ]

  and of_substitution_head head =
    match head with
    | CLF.Substitution.Head.None { location } ->
      of_variant ~name:"CLF.Substitution.Head.None"
        ~data:[ ("location", of_location location) ]
    | CLF.Substitution.Head.Identity { location } ->
      of_variant ~name:"CLF.Substitution.Head.Identity"
        ~data:[ ("location", of_location location) ]
    | CLF.Substitution.Head.Substitution_variable
        { identifier; closure; location } ->
      of_variant ~name:"CLF.Substitution.Head.Substitution_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("closure", of_option of_substitution closure)
          ; ("location", of_location location)
          ]

  and of_substitution_pattern substitution_pattern =
    match substitution_pattern with
    | { CLF.Substitution.Pattern.head; terms; location } ->
      of_variant ~name:"CLF.Substitution"
        ~data:
          [ ("head", of_substitution_pattern_head head)
          ; ("terms", of_list of_term_pattern terms)
          ; ("location", of_location location)
          ]

  and of_substitution_pattern_head head =
    match head with
    | CLF.Substitution.Pattern.Head.None { location } ->
      of_variant ~name:"CLF.Substitution.Pattern.Head.None"
        ~data:[ ("location", of_location location) ]
    | CLF.Substitution.Pattern.Head.Identity { location } ->
      of_variant ~name:"CLF.Substitution.Pattern.Head.Identity"
        ~data:[ ("location", of_location location) ]
    | CLF.Substitution.Pattern.Head.Substitution_variable
        { identifier; closure; location } ->
      of_variant ~name:"CLF.Substitution.Pattern.Head.Substitution_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("closure", of_option of_substitution closure)
          ; ("location", of_location location)
          ]

  and of_context context =
    match context with
    | { CLF.Context.head; bindings; location } ->
      of_variant ~name:"CLF.Context"
        ~data:
          [ ("head", of_context_head head)
          ; ( "bindings"
            , of_list
                (fun (identifier, typ) ->
                  of_association
                    [ ("identifier", of_identifier identifier)
                    ; ("typ", of_option of_typ typ)
                    ])
                bindings )
          ; ("location", of_location location)
          ]

  and of_context_head head =
    match head with
    | CLF.Context.Head.None { location } ->
      of_variant ~name:"CLF.Context.Head.None"
        ~data:[ ("location", of_location location) ]
    | CLF.Context.Head.Hole { location } ->
      of_variant ~name:"CLF.Context.Head.Hole"
        ~data:[ ("location", of_location location) ]
    | CLF.Context.Head.Context_variable { identifier; location } ->
      of_variant ~name:"CLF.Context.Head.Context_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]

  and of_context_pattern context_pattern =
    match context_pattern with
    | { CLF.Context.Pattern.head; bindings; location } ->
      of_variant ~name:"CLF.Context.Pattern"
        ~data:
          [ ("head", of_context_pattern_head head)
          ; ( "bindings"
            , of_list
                (fun (identifier, typ) ->
                  of_association
                    [ ("identifier", of_identifier identifier)
                    ; ("typ", of_typ typ)
                    ])
                bindings )
          ; ("location", of_location location)
          ]

  and of_context_pattern_head head =
    match head with
    | CLF.Context.Pattern.Head.None { location } ->
      of_variant ~name:"CLF.Context.Head.Pattern.None"
        ~data:[ ("location", of_location location) ]
    | CLF.Context.Pattern.Head.Hole { location } ->
      of_variant ~name:"CLF.Context.Head.Pattern.Hole"
        ~data:[ ("location", of_location location) ]
    | CLF.Context.Pattern.Head.Context_variable { identifier; location } ->
      of_variant ~name:"CLF.Context.Pattern.Head.Context_variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
end

module Meta : sig
  open Meta

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_object : Object.t -> Yojson.Safe.t

  val of_pattern : Pattern.t -> Yojson.Safe.t

  val of_context : Context.t -> Yojson.Safe.t

  val of_schema : Schema.t -> Yojson.Safe.t
end = struct
  let rec of_typ typ =
    match typ with
    | Meta.Typ.Context_schema { schema; location } ->
      of_variant ~name:"Meta.Typ.Context_schema"
        ~data:
          [ ("schema", of_schema schema)
          ; ("location", of_location location)
          ]
    | Meta.Typ.Contextual_typ { context; typ; location } ->
      of_variant ~name:"Meta.Typ.Contextual_typ"
        ~data:
          [ ("context", CLF.of_context context)
          ; ("typ", CLF.of_typ typ)
          ; ("location", of_location location)
          ]
    | Meta.Typ.Parameter_typ { context; typ; location } ->
      of_variant ~name:"Meta.Typ.Parameter_typ"
        ~data:
          [ ("context", CLF.of_context context)
          ; ("typ", CLF.of_typ typ)
          ; ("location", of_location location)
          ]
    | Meta.Typ.Plain_substitution_typ { domain; range; location } ->
      of_variant ~name:"Meta.Typ.Plain_substitution_typ"
        ~data:
          [ ("domain", CLF.of_context domain)
          ; ("range", CLF.of_context range)
          ; ("location", of_location location)
          ]
    | Meta.Typ.Renaming_substitution_typ { domain; range; location } ->
      of_variant ~name:"Meta.Typ.Renaming_substitution_typ"
        ~data:
          [ ("domain", CLF.of_context domain)
          ; ("range", CLF.of_context range)
          ; ("location", of_location location)
          ]

  and of_object object_ =
    match object_ with
    | Meta.Object.Context { context; location } ->
      of_variant ~name:"Meta.Object.Context"
        ~data:
          [ ("context", CLF.of_context context)
          ; ("location", of_location location)
          ]
    | Meta.Object.Contextual_term { context; term; location } ->
      of_variant ~name:"Meta.Object.Contextual_term"
        ~data:
          [ ("context", CLF.of_context context)
          ; ("term", CLF.of_term term)
          ; ("location", of_location location)
          ]
    | Meta.Object.Plain_substitution { domain; range; location } ->
      of_variant ~name:"Meta.Object.Plain_substitution"
        ~data:
          [ ("domain", CLF.of_context domain)
          ; ("range", CLF.of_substitution range)
          ; ("location", of_location location)
          ]
    | Meta.Object.Renaming_substitution { domain; range; location } ->
      of_variant ~name:"Meta.Object.Renaming_substitution"
        ~data:
          [ ("domain", CLF.of_context domain)
          ; ("range", CLF.of_substitution range)
          ; ("location", of_location location)
          ]

  and of_pattern pattern =
    match pattern with
    | Meta.Pattern.Context { context; location } ->
      of_variant ~name:"Meta.Pattern.Context"
        ~data:
          [ ("context", CLF.of_context_pattern context)
          ; ("location", of_location location)
          ]
    | Meta.Pattern.Contextual_term { context; term; location } ->
      of_variant ~name:"Meta.Pattern.Contextual_term"
        ~data:
          [ ("context", CLF.of_context_pattern context)
          ; ("term", CLF.of_term_pattern term)
          ; ("location", of_location location)
          ]
    | Meta.Pattern.Plain_substitution { domain; range; location } ->
      of_variant ~name:"Meta.Pattern.Plain_substitution"
        ~data:
          [ ("domain", CLF.of_context_pattern domain)
          ; ("range", CLF.of_substitution_pattern range)
          ; ("location", of_location location)
          ]
    | Meta.Pattern.Renaming_substitution { domain; range; location } ->
      of_variant ~name:"Meta.Pattern.Renaming_substitution"
        ~data:
          [ ("domain", CLF.of_context_pattern domain)
          ; ("range", CLF.of_substitution_pattern range)
          ; ("location", of_location location)
          ]

  and of_context context =
    match context with
    | { Meta.Context.bindings; location } ->
      of_variant ~name:"Meta.Context"
        ~data:
          [ ( "bindings"
            , of_list
                (fun (identifier, typ) ->
                  of_association
                    [ ("identifier", of_identifier identifier)
                    ; ("typ", of_typ typ)
                    ])
                bindings )
          ; ("location", of_location location)
          ]

  and of_schema schema =
    match schema with
    | Meta.Schema.Constant { identifier; location } ->
      of_variant ~name:"Meta.Schema.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("location", of_location location)
          ]
    | Meta.Schema.Alternation { schemas; location } ->
      of_variant ~name:"Meta.Schema.Alternation"
        ~data:
          [ ("schemas", of_list2 of_schema schemas)
          ; ("location", of_location location)
          ]
    | Meta.Schema.Element { some; block; location } ->
      of_variant ~name:"Meta.Schema.Element"
        ~data:
          [ ( "some"
            , of_option
                (of_list1 (fun (identifier, typ) ->
                     of_association
                       [ ("identifier", of_identifier identifier)
                       ; ("typ", CLF.of_typ typ)
                       ]))
                some )
          ; ( "block"
            , match block with
              | `Unnamed typ -> CLF.of_typ typ
              | `Record bindings ->
                of_list1
                  (fun (identifier, typ) ->
                    of_association
                      [ ("identifier", of_identifier identifier)
                      ; ("typ", CLF.of_typ typ)
                      ])
                  bindings )
          ; ("location", of_location location)
          ]
end

module Comp : sig
  open Comp

  val of_kind : Kind.t -> Yojson.Safe.t

  val of_typ : Typ.t -> Yojson.Safe.t

  val of_expression : Expression.t -> Yojson.Safe.t

  val of_pattern : Pattern.t -> Yojson.Safe.t

  val of_context : Context.t -> Yojson.Safe.t
end = struct
  let rec of_kind kind =
    match kind with
    | Comp.Kind.Ctype { location } ->
      of_variant ~name:"Comp.Kind.Ctype"
        ~data:[ ("location", of_location location) ]
    | Comp.Kind.Arrow { domain; range; location } ->
      of_variant ~name:"Comp.Kind.Arrow"
        ~data:
          [ ("domain", of_typ domain)
          ; ("range", of_kind range)
          ; ("location", of_location location)
          ]
    | Comp.Kind.Pi
        { parameter_identifier; plicity; parameter_type; body; location } ->
      of_variant ~name:"Comp.Kind.Pi"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("plicity", of_plicity plicity)
          ; ("parameter_type", Meta.of_typ parameter_type)
          ; ("body", of_kind body)
          ; ("location", of_location location)
          ]

  and of_typ typ =
    match typ with
    | Comp.Typ.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"Comp.Typ.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | Comp.Typ.Pi
        { parameter_identifier; plicity; parameter_type; body; location } ->
      of_variant ~name:"Comp.Typ.Pi"
        ~data:
          [ ("parameter_identifier", of_identifier_opt parameter_identifier)
          ; ("plicity", of_plicity plicity)
          ; ("parameter_type", Meta.of_typ parameter_type)
          ; ("body", of_typ body)
          ; ("location", of_location location)
          ]
    | Comp.Typ.Arrow { domain; range; orientation; location } ->
      of_variant ~name:"Comp.Typ.Arrow"
        ~data:
          [ ("domain", of_typ domain)
          ; ("range", of_typ range)
          ; ( "orientation"
            , match orientation with
              | `Forward -> of_string "forward"
              | `Backward -> of_string "backward" )
          ; ("location", of_location location)
          ]
    | Comp.Typ.Cross { types; location } ->
      of_variant ~name:"Comp.Typ.Cross"
        ~data:
          [ ("types", of_list2 of_typ types)
          ; ("location", of_location location)
          ]
    | Comp.Typ.Box { meta_type; location } ->
      of_variant ~name:"Comp.Typ.Box"
        ~data:
          [ ("meta_type", Meta.of_typ meta_type)
          ; ("location", of_location location)
          ]
    | Comp.Typ.Base { applicand; arguments; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"Comp.Typ.Base"
        ~data:
          [ ("applicand", of_qualified_identifier applicand)
          ; ("arguments", of_list Meta.of_object arguments)
          ; ("location", of_location location)
          ]
    | Comp.Typ.Cobase { applicand; arguments; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"Comp.Typ.Cobase"
        ~data:
          [ ("applicand", of_qualified_identifier applicand)
          ; ("arguments", of_list Meta.of_object arguments)
          ; ("location", of_location location)
          ]

  and of_expression expression =
    match expression with
    | Comp.Expression.Variable { identifier; location } ->
      of_variant ~name:"Comp.Expression.Variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Constant { identifier; quoted; location; operator = _ }
      ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"Comp.Expression.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Fn { parameters; body; location } ->
      of_variant ~name:"Comp.Expression.Fn"
        ~data:
          [ ("parameters", of_list1 of_identifier_opt parameters)
          ; ("body", of_expression body)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Mlam { parameters; body; location } ->
      of_variant ~name:"Comp.Expression.Mlam"
        ~data:
          [ ( "parameters"
            , of_list1 Fun.(Pair.fst >> of_identifier_opt) parameters )
          ; ("body", of_expression body)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Fun { branches; location } ->
      of_variant ~name:"Comp.Expression.Fun"
        ~data:
          [ ( "branchs"
            , of_list1
                (fun (patterns, body) ->
                  of_association
                    [ ("patterns", of_list1 of_pattern patterns)
                    ; ("body", of_expression body)
                    ])
                branches )
          ; ("location", of_location location)
          ]
    | Comp.Expression.Let { pattern; scrutinee; body; location } ->
      of_variant ~name:"Comp.Expression.Let"
        ~data:
          [ ("pattern", of_pattern pattern)
          ; ("scrutinee", of_expression scrutinee)
          ; ("body", of_expression body)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Box { meta_object; location } ->
      of_variant ~name:"Comp.Expression.Box"
        ~data:
          [ ("meta_object", Meta.of_object meta_object)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Impossible { scrutinee; location } ->
      of_variant ~name:"Comp.Expression.Impossible"
        ~data:
          [ ("scrutinee", of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Case { scrutinee; check_coverage; branches; location }
      ->
      of_variant ~name:"Comp.Expression.Case"
        ~data:
          [ ("scrutinee", of_expression scrutinee)
          ; ("check_coverage", of_bool check_coverage)
          ; ( "branches"
            , of_list1
                (fun (pattern, body) ->
                  of_association
                    [ ("pattern", of_pattern pattern)
                    ; ("body", of_expression body)
                    ])
                branches )
          ; ("location", of_location location)
          ]
    | Comp.Expression.Tuple { elements; location } ->
      of_variant ~name:"Comp.Expression.Tuple"
        ~data:
          [ ("elements", of_list2 of_expression elements)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Hole { label; location } ->
      of_variant ~name:"Comp.Expression.Hole"
        ~data:
          [ ("label", of_identifier_opt label)
          ; ("location", of_location location)
          ]
    | Comp.Expression.BoxHole { location } ->
      of_variant ~name:"Comp.Expression.BoxHole"
        ~data:[ ("location", of_location location) ]
    | Comp.Expression.Application { applicand; arguments; location } ->
      of_variant ~name:"Comp.Expression.Application"
        ~data:
          [ ("applicand", of_expression applicand)
          ; ("arguments", of_list1 of_expression arguments)
          ; ("location", of_location location)
          ]
    | Comp.Expression.Observation { observation; arguments; location } ->
      of_variant ~name:"Comp.Expression.Observation"
        ~data:
          [ ("observation", of_qualified_identifier observation)
          ; ("arguments", of_list of_expression arguments)
          ; ("location", of_location location)
          ]
    | Comp.Expression.TypeAnnotated { expression; typ; location } ->
      of_variant ~name:"Comp.Expression.TypeAnnotated"
        ~data:
          [ ("expression", of_expression expression)
          ; ("typ", of_typ typ)
          ; ("location", of_location location)
          ]

  and of_pattern pattern =
    match pattern with
    | Comp.Pattern.Variable { identifier; location } ->
      of_variant ~name:"Comp.Pattern.Variable"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.Constant { identifier; quoted; location; operator = _ } ->
      (* Don't serialize [operator] since it is resolved from the
         signature. *)
      of_variant ~name:"Comp.Pattern.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("quoted", of_bool quoted)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.MetaObject { meta_pattern; location } ->
      of_variant ~name:"Comp.Pattern.MetaObject"
        ~data:
          [ ("meta_pattern", Meta.of_pattern meta_pattern)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.Tuple { elements; location } ->
      of_variant ~name:"Comp.Pattern.Tuple"
        ~data:
          [ ("elements", of_list2 of_pattern elements)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.Application { applicand; arguments; location } ->
      of_variant ~name:"Comp.Pattern.Application"
        ~data:
          [ ("applicand", of_pattern applicand)
          ; ("arguments", of_list1 of_pattern arguments)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.Observation { observation; arguments; location } ->
      of_variant ~name:"Comp.Pattern.Observation"
        ~data:
          [ ("observation", of_qualified_identifier observation)
          ; ("arguments", of_list of_pattern arguments)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.TypeAnnotated { pattern; typ; location } ->
      of_variant ~name:"Comp.Pattern.TypeAnnotated"
        ~data:
          [ ("pattern", of_pattern pattern)
          ; ("typ", of_typ typ)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.MetaTypeAnnotated
        { annotation_identifier; annotation_type; body; location } ->
      of_variant ~name:"Comp.Pattern.MetaTypeAnnotated"
        ~data:
          [ ("annotation_identifier", of_identifier annotation_identifier)
          ; ("annotation_type", Meta.of_typ annotation_type)
          ; ("body", of_pattern body)
          ; ("location", of_location location)
          ]
    | Comp.Pattern.Wildcard { location } ->
      of_variant ~name:"Comp.Pattern.Wildcard"
        ~data:[ ("location", of_location location) ]

  and of_context context =
    match context with
    | { Comp.Context.bindings; location } ->
      of_variant ~name:"Comp.Context"
        ~data:
          [ ( "bindings"
            , of_list
                (fun (identifier, typ) ->
                  of_association
                    [ ("identifier", of_identifier identifier)
                    ; ("typ", of_typ typ)
                    ])
                bindings )
          ; ("location", of_location location)
          ]
end

module Harpoon : sig
  open Harpoon

  val of_proof : Proof.t -> Yojson.Safe.t

  val of_command : Command.t -> Yojson.Safe.t

  val of_directive : Directive.t -> Yojson.Safe.t

  val of_split_branch : Split_branch.t -> Yojson.Safe.t

  val of_split_branch_label : Split_branch.Label.t -> Yojson.Safe.t

  val of_suffices_branch : Suffices_branch.t -> Yojson.Safe.t

  val of_hypothetical : Hypothetical.t -> Yojson.Safe.t

  val of_repl_command : Repl.Command.t -> Yojson.Safe.t
end = struct
  let rec of_proof proof =
    match proof with
    | Harpoon.Proof.Incomplete { label; location } ->
      of_variant ~name:"Harpoon.Proof.Incomplete"
        ~data:
          [ ("label", of_identifier_opt label)
          ; ("location", of_location location)
          ]
    | Harpoon.Proof.Command { command; body; location } ->
      of_variant ~name:"Harpoon.Proof.Command"
        ~data:
          [ ("command", of_command command)
          ; ("body", of_proof body)
          ; ("location", of_location location)
          ]
    | Harpoon.Proof.Directive { directive; location } ->
      of_variant ~name:"Harpoon.Proof.Directive"
        ~data:
          [ ("directive", of_directive directive)
          ; ("location", of_location location)
          ]

  and of_command command =
    match command with
    | Harpoon.Command.By { expression; assignee; location } ->
      of_variant ~name:"Harpoon.Command.By"
        ~data:
          [ ("expression", Comp.of_expression expression)
          ; ("assignee", of_identifier assignee)
          ; ("location", of_location location)
          ]
    | Harpoon.Command.Unbox { expression; assignee; modifier; location } ->
      of_variant ~name:"Harpoon.Command.Unbox"
        ~data:
          [ ("expression", Comp.of_expression expression)
          ; ("assignee", of_identifier assignee)
          ; ( "modifier"
            , match modifier with
              | Option.Some `Strengthened -> of_string "strengthened"
              | Option.None -> `Null )
          ; ("location", of_location location)
          ]

  and of_directive directive =
    match directive with
    | Harpoon.Directive.Intros { hypothetical; location } ->
      of_variant ~name:"Harpoon.Directive.Intros"
        ~data:
          [ ("hypothetical", of_hypothetical hypothetical)
          ; ("location", of_location location)
          ]
    | Harpoon.Directive.Solve { solution; location } ->
      of_variant ~name:"Harpoon.Directive.Solve"
        ~data:
          [ ("solution", Comp.of_expression solution)
          ; ("location", of_location location)
          ]
    | Harpoon.Directive.Split { scrutinee; branches; location } ->
      of_variant ~name:"Harpoon.Directive.Split"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("branches", of_list1 of_split_branch branches)
          ; ("location", of_location location)
          ]
    | Harpoon.Directive.Impossible { scrutinee; location } ->
      of_variant ~name:"Harpoon.Directive.Impossible"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Harpoon.Directive.Suffices { scrutinee; branches; location } ->
      of_variant ~name:"Harpoon.Directive.Suffices"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("branches", of_list of_suffices_branch branches)
          ; ("location", of_location location)
          ]

  and of_split_branch split_branch =
    match split_branch with
    | { Harpoon.Split_branch.label; body; location } ->
      of_variant ~name:"Harpoon.Split_branch"
        ~data:
          [ ("label", of_split_branch_label label)
          ; ("body", of_hypothetical body)
          ; ("location", of_location location)
          ]

  and of_split_branch_label split_branch_label =
    match split_branch_label with
    | Harpoon.Split_branch.Label.Constant { identifier; location } ->
      of_variant ~name:"Harpoon.Split_branch.Label.Constant"
        ~data:
          [ ("identifier", of_qualified_identifier identifier)
          ; ("location", of_location location)
          ]
    | Harpoon.Split_branch.Label.Bound_variable { location } ->
      of_variant ~name:"Harpoon.Split_branch.Label.Bound_variable"
        ~data:[ ("location", of_location location) ]
    | Harpoon.Split_branch.Label.Empty_context { location } ->
      of_variant ~name:"Harpoon.Split_branch.Label.Empty_context"
        ~data:[ ("location", of_location location) ]
    | Harpoon.Split_branch.Label.Extended_context
        { schema_element; location } ->
      of_variant ~name:"Harpoon.Split_branch.Label.Extended_context"
        ~data:
          [ ("schema_element", of_int schema_element)
          ; ("location", of_location location)
          ]
    | Harpoon.Split_branch.Label.Parameter_variable
        { schema_element; projection; location } ->
      of_variant ~name:"Harpoon.Split_branch.Label.Parameter_variable"
        ~data:
          [ ("schema_element", of_int schema_element)
          ; ("projection", of_option of_int projection)
          ; ("location", of_location location)
          ]

  and of_suffices_branch suffices_branch =
    match suffices_branch with
    | { Harpoon.Suffices_branch.goal; proof; location } ->
      of_variant ~name:"Harpoon.Suffices_branch"
        ~data:
          [ ("goal", Comp.of_typ goal)
          ; ("proof", of_proof proof)
          ; ("location", of_location location)
          ]

  and of_hypothetical hypothetical =
    match hypothetical with
    | { Harpoon.Hypothetical.meta_context; comp_context; proof; location } ->
      of_variant ~name:"Harpoon.Hypothetical"
        ~data:
          [ ("meta_context", Meta.of_context meta_context)
          ; ("comp_context", Comp.of_context comp_context)
          ; ("proof", of_proof proof)
          ; ("location", of_location location)
          ]

  and of_repl_command command =
    match command with
    | Harpoon.Repl.Command.Rename { rename_from; rename_to; level; location }
      ->
      of_variant ~name:"Harpoon.Repl.Command.Rename"
        ~data:
          [ ("rename_from", of_identifier rename_from)
          ; ("rename_to", of_identifier rename_to)
          ; ( "level"
            , match level with
              | `meta -> of_string "meta"
              | `comp -> of_string "comp" )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.ToggleAutomation { kind; change; location } ->
      of_variant ~name:"Harpoon.Repl.Command.ToggleAutomation"
        ~data:
          [ ( "kind"
            , match kind with
              | `auto_intros -> of_string "auto_intros"
              | `auto_solve_trivial -> of_string " auto_solve_trivial" )
          ; ( "change"
            , match change with
              | `off -> of_string "off"
              | `on -> of_string "on"
              | `toggle -> of_string "toggle" )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Type { scrutinee; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Type"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Info { kind; object_identifier; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Info"
        ~data:
          [ ( "kind"
            , match kind with
              | `prog -> of_string "prog" )
          ; ("object_identifier", of_qualified_identifier object_identifier)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.SelectTheorem { theorem; location } ->
      of_variant ~name:"Harpoon.Repl.Command.SelectTheorem"
        ~data:
          [ ("theorem", of_qualified_identifier theorem)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Theorem { subcommand; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Theorem"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `defer -> of_string "defer"
              | `dump_proof file -> of_string file
              | `list -> of_string "list"
              | `show_ihs -> of_string "show_ihs"
              | `show_proof -> of_string "show_proof" )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Session { subcommand; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Session"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `create -> of_string "create"
              | `defer -> of_string "defer"
              | `list -> of_string "list"
              | `serialize -> of_string "serialize" )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Subgoal { subcommand; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Subgoal"
        ~data:
          [ ( "subcommand"
            , match subcommand with
              | `defer -> of_string "defer"
              | `list -> of_string "list" )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Undo { location } ->
      of_variant ~name:"Harpoon.Repl.Command.Undo"
        ~data:[ ("location", of_location location) ]
    | Harpoon.Repl.Command.Redo { location } ->
      of_variant ~name:"Harpoon.Repl.Command.Redo"
        ~data:[ ("location", of_location location) ]
    | Harpoon.Repl.Command.History { location } ->
      of_variant ~name:"Harpoon.Repl.Command.History"
        ~data:[ ("location", of_location location) ]
    | Harpoon.Repl.Command.Translate { theorem; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Translate"
        ~data:
          [ ("theorem", of_qualified_identifier theorem)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Intros { introduced_variables; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Intros"
        ~data:
          [ ( "introduced_variables"
            , of_option (of_list1 of_identifier) introduced_variables )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Split { scrutinee; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Split"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Invert { scrutinee; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Invert"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Impossible { scrutinee; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Impossible"
        ~data:
          [ ("scrutinee", Comp.of_expression scrutinee)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.MSplit { identifier; location } ->
      of_variant ~name:"Harpoon.Repl.Command.MSplit"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Solve { solution; location } ->
      of_variant ~name:"Harpoon.Repl.Command.Solve"
        ~data:
          [ ("solution", Comp.of_expression solution)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Unbox { expression; assignee; modifier; location }
      ->
      of_variant ~name:"Harpoon.Repl.Command.Unbox"
        ~data:
          [ ("expression", Comp.of_expression expression)
          ; ("assignee", of_identifier assignee)
          ; ( "modifier"
            , of_option
                (function
                  | `Strengthened -> of_string "strengthened")
                modifier )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.By { expression; assignee; location } ->
      of_variant ~name:"Harpoon.Repl.Command.By"
        ~data:
          [ ("expression", Comp.of_expression expression)
          ; ("assignee", of_identifier assignee)
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Suffices { implication; goal_premises; location }
      ->
      of_variant ~name:"Harpoon.Repl.Command.Suffices"
        ~data:
          [ ("implication", Comp.of_expression implication)
          ; ( "goal_premises"
            , of_list
                (function
                  | `exact typ -> Comp.of_typ typ
                  | `infer location -> of_location location)
                goal_premises )
          ; ("location", of_location location)
          ]
    | Harpoon.Repl.Command.Help { location } ->
      of_variant ~name:"Harpoon.Repl.Command.Help"
        ~data:[ ("location", of_location location) ]
end

module Signature : sig
  open Signature

  val of_pragma : Pragma.t -> Yojson.Safe.t

  val of_global_pragma : Pragma.Global.t -> Yojson.Safe.t

  val of_totality_declaration : Totality.Declaration.t -> Yojson.Safe.t

  val of_numeric_totality_order : Int.t Totality.Order.t -> Yojson.Safe.t

  val of_named_totality_order :
    Identifier.t Totality.Order.t -> Yojson.Safe.t

  val of_declaration : Declaration.t -> Yojson.Safe.t

  val of_signature : Signature.t -> Yojson.Safe.t
end = struct
  let rec of_pragma pragma =
    match pragma with
    | Signature.Pragma.Name
        { constant; meta_variable_base; computation_variable_base; location }
      ->
      of_variant ~name:"Signature.Pragma.Name"
        ~data:
          [ ("constant", of_qualified_identifier constant)
          ; ("meta_variable_base", of_identifier meta_variable_base)
          ; ( "computation_variable_base"
            , of_option of_identifier computation_variable_base )
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Default_associativity { associativity; location } ->
      of_variant ~name:"Signature.Pragma.Default_associativity"
        ~data:
          [ ("associativity", of_associativity associativity)
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Prefix_fixity { constant; precedence; location } ->
      of_variant ~name:"Signature.Pragma.Prefix_fixity"
        ~data:
          [ ("constant", of_qualified_identifier constant)
          ; ("precedence", of_option of_int precedence)
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Infix_fixity
        { constant; precedence; associativity; location } ->
      of_variant ~name:"Signature.Pragma.Infix_fixity"
        ~data:
          [ ("constant", of_qualified_identifier constant)
          ; ("associativity", of_option of_associativity associativity)
          ; ("precedence", of_option of_int precedence)
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Postfix_fixity { constant; precedence; location } ->
      of_variant ~name:"Signature.Pragma.Postfix_fixity"
        ~data:
          [ ("constant", of_qualified_identifier constant)
          ; ("precedence", of_option of_int precedence)
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Not { location } ->
      of_variant ~name:"Signature.Pragma.Not"
        ~data:[ ("location", of_location location) ]
    | Signature.Pragma.Open_module { module_identifier; location } ->
      of_variant ~name:"Signature.Pragma.Open_module"
        ~data:
          [ ("module_identifier", of_qualified_identifier module_identifier)
          ; ("location", of_location location)
          ]
    | Signature.Pragma.Abbreviation
        { module_identifier; abbreviation; location } ->
      of_variant ~name:"Signature.Pragma.Abbreviation"
        ~data:
          [ ("module_identifier", of_qualified_identifier module_identifier)
          ; ("abbreviation", of_identifier abbreviation)
          ; ("location", of_location location)
          ]

  and of_global_pragma global_pragma =
    match global_pragma with
    | Signature.Pragma.Global.No_strengthening { location } ->
      of_variant ~name:"Signature.Pragma.Global.No_strengthening"
        ~data:[ ("location", of_location location) ]
    | Signature.Pragma.Global.Coverage { variant; location } ->
      of_variant ~name:"Signature.Pragma.Global.Coverage"
        ~data:
          [ ( "variant"
            , match variant with
              | `Error -> of_string "error"
              | `Warn -> of_string "warn" )
          ; ("location", of_location location)
          ]

  and of_totality_declaration totality_declaration =
    match totality_declaration with
    | Signature.Totality.Declaration.Trust { location } ->
      of_variant ~name:"Signature.Totality.Declaration.Trust"
        ~data:[ ("location", of_location location) ]
    | Signature.Totality.Declaration.Numeric { order; location } ->
      of_variant ~name:"Signature.Totality.Declaration.Numeric"
        ~data:
          [ ("order", of_option of_numeric_totality_order order)
          ; ("location", of_location location)
          ]
    | Signature.Totality.Declaration.Named
        { order; program; argument_labels; location } ->
      of_variant ~name:"Signature.Totality.Declaration.Named"
        ~data:
          [ ("order", of_option of_named_totality_order order)
          ; ("program", of_identifier program)
          ; ("argument_labels", of_list of_identifier_opt argument_labels)
          ; ("location", of_location location)
          ]

  and of_numeric_totality_order totality_order =
    match totality_order with
    | Signature.Totality.Order.Argument { argument; location } ->
      of_variant ~name:"Signature.Order.Argument"
        ~data:
          [ ("argument", of_int argument)
          ; ("location", of_location location)
          ]
    | Signature.Totality.Order.Lexical_ordering { arguments; location } ->
      of_variant ~name:"Signature.Totality.Order.Lexical_ordering"
        ~data:
          [ ("arguments", of_list1 of_numeric_totality_order arguments)
          ; ("location", of_location location)
          ]
    | Signature.Totality.Order.Simultaneous_ordering { arguments; location }
      ->
      of_variant ~name:"Signature.Totality.Order.Simultaneous_ordering"
        ~data:
          [ ("arguments", of_list1 of_numeric_totality_order arguments)
          ; ("location", of_location location)
          ]

  and of_named_totality_order totality_order =
    match totality_order with
    | Signature.Totality.Order.Argument { argument; location } ->
      of_variant ~name:"Signature.Order.Argument"
        ~data:
          [ ("argument", of_identifier argument)
          ; ("location", of_location location)
          ]
    | Signature.Totality.Order.Lexical_ordering { arguments; location } ->
      of_variant ~name:"Signature.Totality.Order.Lexical_ordering"
        ~data:
          [ ("arguments", of_list1 of_named_totality_order arguments)
          ; ("location", of_location location)
          ]
    | Signature.Totality.Order.Simultaneous_ordering { arguments; location }
      ->
      of_variant ~name:"Signature.Totality.Order.Simultaneous_ordering"
        ~data:
          [ ("arguments", of_list1 of_named_totality_order arguments)
          ; ("location", of_location location)
          ]

  and of_declaration declaration =
    match declaration with
    | Signature.Declaration.Typ { identifier; kind; location } ->
      of_variant ~name:"Signature.Declaration.Typ"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("kind", LF.of_kind kind)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Const { identifier; typ; location } ->
      of_variant ~name:"Signature.Declaration.Const"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("typ", LF.of_typ typ)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.CompTyp
        { identifier; kind; datatype_flavour; location } ->
      of_variant ~name:"Signature.Declaration.CompTyp"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("kind", Comp.of_kind kind)
          ; ( "datatype_flavour"
            , match datatype_flavour with
              | `Inductive -> of_string "inductive"
              | `Stratified -> of_string "stratified" )
          ; ("location", of_location location)
          ]
    | Signature.Declaration.CompCotyp { identifier; kind; location } ->
      of_variant ~name:"Signature.Declaration.CompCotyp"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("kind", Comp.of_kind kind)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.CompConst { identifier; typ; location } ->
      of_variant ~name:"Signature.Declaration.CompConst"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("typ", Comp.of_typ typ)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.CompDest
        { identifier; observation_type; return_type; location } ->
      of_variant ~name:"Signature.Declaration.CompDest"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("observation_type", Comp.of_typ observation_type)
          ; ("return_type", Comp.of_typ return_type)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.CompTypAbbrev { identifier; kind; typ; location }
      ->
      of_variant ~name:"Signature.Declaration.CompTypAbbrev"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("kind", Comp.of_kind kind)
          ; ("typ", Comp.of_typ typ)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Schema { identifier; schema; location } ->
      of_variant ~name:"Signature.Declaration.Schema"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("schema", Meta.of_schema schema)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Pragma { pragma; location } ->
      of_variant ~name:"Signature.Declaration.Pragma"
        ~data:
          [ ("pragma", of_pragma pragma)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.GlobalPragma { pragma; location } ->
      of_variant ~name:"Signature.Declaration.GlobalPragma"
        ~data:
          [ ("pragma", of_global_pragma pragma)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Theorem
        { location; identifier; typ; order; body } ->
      of_variant ~name:"Signature.Declaration.Theorem"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("typ", Comp.of_typ typ)
          ; ("order", of_option of_totality_declaration order)
          ; ("body", Comp.of_expression body)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Proof { location; identifier; typ; order; body }
      ->
      of_variant ~name:"Signature.Declaration.Proof"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("typ", Comp.of_typ typ)
          ; ("order", of_option of_totality_declaration order)
          ; ("body", Harpoon.of_proof body)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Recursive_declarations { declarations; location }
      ->
      of_variant ~name:"Signature.Declaration.Recursive_declarations"
        ~data:
          [ ("declarations", of_list1 of_declaration declarations)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Val { identifier; typ; expression; location } ->
      of_variant ~name:"Signature.Declaration.Val"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("typ", of_option Comp.of_typ typ)
          ; ("expression", Comp.of_expression expression)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Query
        { identifier
        ; meta_context
        ; typ
        ; expected_solutions
        ; maximum_tries
        ; location
        } ->
      of_variant ~name:"Signature.Declaration.Query"
        ~data:
          [ ("identifier", of_option of_identifier identifier)
          ; ("meta_context", Meta.of_context meta_context)
          ; ("typ", LF.of_typ typ)
          ; ("expected_solutions", of_option of_int expected_solutions)
          ; ("maximum_tries", of_option of_int maximum_tries)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.MQuery
        { identifier
        ; typ
        ; expected_solutions
        ; search_tries
        ; search_depth
        ; location
        } ->
      of_variant ~name:"Signature.Declaration.MQuery"
        ~data:
          [ ("identifier", of_option of_identifier identifier)
          ; ("typ", Comp.of_typ typ)
          ; ("expected_solutions", of_option of_int expected_solutions)
          ; ("search_tries", of_option of_int search_tries)
          ; ("search_depth", of_option of_int search_depth)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Module { identifier; declarations; location } ->
      of_variant ~name:"Signature.Declaration.Module"
        ~data:
          [ ("identifier", of_identifier identifier)
          ; ("declarations", of_list of_declaration declarations)
          ; ("location", of_location location)
          ]
    | Signature.Declaration.Comment { content; location } ->
      of_variant ~name:"Signature.Declaration.Comment"
        ~data:
          [ ("content", of_string content)
          ; ("location", of_location location)
          ]

  and of_signature signature =
    of_variant ~name:"Signature"
      ~data:[ ("declarations", of_list of_declaration signature) ]
end
