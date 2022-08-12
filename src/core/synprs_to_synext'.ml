open Support

module Operator : sig
  type t

  (** {1 Destructors} *)

  val identifier : t -> QualifiedIdentifier.t

  val arity : t -> Int.t

  val precedence : t -> Int.t

  val fixity : t -> Fixity.t

  val associativity : t -> Associativity.t

  val location : t -> Location.t

  (** {1 Constructors} *)

  val make_prefix :
    identifier:QualifiedIdentifier.t -> arity:Int.t -> precedence:Int.t -> t

  val make_infix :
       identifier:QualifiedIdentifier.t
    -> associativity:Associativity.t
    -> precedence:Int.t
    -> t

  val make_postfix :
    identifier:QualifiedIdentifier.t -> arity:Int.t -> precedence:Int.t -> t

  val as_prefix : t -> t

  (** {1 Instances} *)

  include Eq.EQ with type t := t
end = struct
  type t =
    { identifier : QualifiedIdentifier.t
    ; arity : Int.t
    ; precedence : Int.t
    ; fixity : Fixity.t
    ; associativity : Associativity.t
    }

  let[@inline] identifier { identifier; _ } = identifier

  let[@inline] arity { arity; _ } = arity

  let[@inline] precedence { precedence; _ } = precedence

  let[@inline] fixity { fixity; _ } = fixity

  let[@inline] associativity { associativity; _ } = associativity

  let[@inline] location { identifier; _ } =
    QualifiedIdentifier.location identifier

  let make_prefix ~identifier ~arity ~precedence =
    { identifier
    ; arity
    ; precedence
    ; fixity = Fixity.prefix
    ; associativity = Associativity.right_associative
    }

  let make_infix ~identifier ~associativity ~precedence =
    { identifier
    ; arity = 2
    ; precedence
    ; fixity = Fixity.infix
    ; associativity
    }

  let make_postfix ~identifier ~arity ~precedence =
    { identifier
    ; arity
    ; precedence
    ; fixity = Fixity.postfix
    ; associativity = Associativity.left_associative
    }

  let as_prefix operator =
    { operator with
      fixity = Fixity.prefix
    ; associativity = Associativity.right_associative
    }

  include (
    (val Eq.contramap (module QualifiedIdentifier) identifier) :
      Eq.EQ with type t := t)
end

(** A dictionary is a persistent hash map data structure to represent entries
    currently in scope during the data-dependent elaboration from the parser
    syntax to the external syntax. Modules are represented as
    sub-dictionaries for performance. *)
module Dictionary : sig
  type t

  type entry = private
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | Module of t

  (** {1 Constructors} *)

  val empty : t

  val add_term : Identifier.t -> t -> t

  val add_prefix_lf_type_constant :
    arity:Int.t -> precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_infix_lf_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> QualifiedIdentifier.t
    -> t
    -> t

  val add_postfix_lf_type_constant :
    arity:Int.t -> precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_prefix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_infix_lf_term_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> QualifiedIdentifier.t
    -> t
    -> t

  val add_postfix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_module : t -> QualifiedIdentifier.t -> t -> t

  (** {1 Lookup} *)

  val lookup : QualifiedIdentifier.t -> t -> entry Option.t

  (** {1 Interoperability} *)

  (** [to_seq dictionary] is [dictionary] flattened to a sequence of bindings
      by qualified name. There is no guarantee on the order of bindings in
      the resultant sequence. *)
  val to_seq : t -> (QualifiedIdentifier.t * entry) Seq.t
end = struct
  type t = entry Identifier.Hamt.t

  and entry =
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | Module of t

  let empty = Identifier.Hamt.empty

  let add_entry entry identifier dictionary =
    Identifier.Hamt.add identifier entry dictionary

  let add_nested_entry entry qualified_identifier dictionary =
    let name = QualifiedIdentifier.name qualified_identifier
    and modules = QualifiedIdentifier.modules qualified_identifier in
    match modules with
    | [] (* Toplevel declaration *) -> add_entry entry name dictionary
    | m :: ms (* Nested declaration *) ->
      let rec add module_name_to_lookup next_modules dictionary =
        let dictionary' =
          match
            Identifier.Hamt.find_opt module_name_to_lookup dictionary
          with
          | Option.Some (Module dictionary')
          (* Addition to existing module *) -> dictionary'
          | Option.Some _ (* Entry shadowing *)
          | Option.None (* Module introduction *) -> empty
        in
        match next_modules with
        | [] (* Finished lookups *) ->
          add_entry
            (Module (add_entry entry name dictionary'))
            module_name_to_lookup dictionary
        | m :: ms (* Recursively lookup next module *) ->
          add_entry
            (Module (add m ms dictionary'))
            module_name_to_lookup dictionary
      in
      add m ms dictionary

  let add_term = add_entry LF_term

  let add_prefix_lf_type_constant ~arity ~precedence identifier =
    add_nested_entry
      (LF_type_constant (Operator.make_prefix ~identifier ~arity ~precedence))
      identifier

  let add_infix_lf_type_constant ~associativity ~precedence identifier =
    add_nested_entry
      (LF_type_constant
         (Operator.make_infix ~identifier ~associativity ~precedence))
      identifier

  let add_postfix_lf_type_constant ~arity ~precedence identifier =
    add_nested_entry
      (LF_type_constant
         (Operator.make_postfix ~identifier ~arity ~precedence))
      identifier

  let add_prefix_lf_term_constant ~arity ~precedence identifier =
    add_nested_entry
      (LF_term_constant (Operator.make_prefix ~identifier ~arity ~precedence))
      identifier

  let add_infix_lf_term_constant ~associativity ~precedence identifier =
    add_nested_entry
      (LF_term_constant
         (Operator.make_infix ~identifier ~associativity ~precedence))
      identifier

  let add_postfix_lf_term_constant ~arity ~precedence identifier =
    add_nested_entry
      (LF_term_constant
         (Operator.make_postfix ~identifier ~arity ~precedence))
      identifier

  let add_module module_dictionary identifier =
    add_nested_entry (Module module_dictionary) identifier

  let lookup qualified_identifier dictionary =
    let name = QualifiedIdentifier.name qualified_identifier
    and modules = QualifiedIdentifier.modules qualified_identifier in
    let rec lookup modules dictionary =
      match modules with
      | [] (* Toplevel declaration *) ->
        Identifier.Hamt.find_opt name dictionary
      | m :: ms (* Nested declaration *) -> (
        match Identifier.Hamt.find_opt m dictionary with
        | Option.Some (Module dictionary') -> lookup ms dictionary'
        | Option.Some _ (* Expected a module *) | Option.None (* Unbound *)
          -> Option.none)
    in
    lookup modules dictionary

  let rec to_seq dictionary =
    dictionary |> Identifier.Hamt.bindings |> List.to_seq
    |> Seq.flat_map (function
         | identifier, (Module nested_dictionary as entry) ->
           nested_dictionary |> to_seq
           |> Seq.map (fun (nested_entry_identifier, entry) ->
                  let identifier =
                    QualifiedIdentifier.prepend_module identifier
                      nested_entry_identifier
                  in
                  (identifier, entry))
           |> Seq.cons (QualifiedIdentifier.make_simple identifier, entry)
         | identifier, entry ->
           let identifier = QualifiedIdentifier.make_simple identifier in
           Seq.return (identifier, entry))
end

exception Unbound_qualified_identifier of QualifiedIdentifier.t

module LF = struct
  (* Exceptions for LF kind elaboration *)

  exception Illegal_identifier_kind of Location.t

  exception Illegal_qualified_identifier_kind of Location.t

  exception Illegal_backward_arrow_kind of Location.t

  exception Illegal_hole_kind of Location.t

  exception Illegal_lambda_kind of Location.t

  exception Illegal_annotated_kind of Location.t

  exception Illegal_application_kind of Location.t

  exception Illegal_untyped_pi_kind of Location.t

  (* Exceptions for LF type elaboration *)

  exception Illegal_type_kind_type of Location.t

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception Unbound_type_constant of Location.t * QualifiedIdentifier.t

  (* Exceptions for LF term elaboration *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Unbound_term_constant of Location.t * QualifiedIdentifier.t

  (* Exceptions for application rewriting *)

  exception Expected_term_constant of Location.t * Dictionary.entry

  exception Expected_type_constant of Location.t * Dictionary.entry

  exception Expected_term of Synext'.LF.Typ.t

  exception Expected_type of Synext'.LF.Term.t

  exception Empty_expression

  exception Misplaced_operator of Location.t * Location.t List.t

  exception Consecutive_non_associative_operators of Location.t * Location.t

  exception Arity_mismatch of Location.t * Location.t List.t

  exception Leftover_expressions of Location.t List2.t

  (* Elaboration *)

  let rec elaborate_kind dictionary object_ =
    match object_ with
    | Synprs.LF.Object.RawIdentifier { location; identifier; _ } ->
      raise @@ Illegal_identifier_kind location
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier; _ } ->
      raise @@ Illegal_qualified_identifier_kind location
    | Synprs.LF.Object.RawBackwardArrow { location; _ } ->
      raise @@ Illegal_backward_arrow_kind location
    | Synprs.LF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_kind location
    | Synprs.LF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_kind location
    | Synprs.LF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_kind location
    | Synprs.LF.Object.RawApplication { location; _ } ->
      raise @@ Illegal_application_kind location
    | Synprs.LF.Object.RawPi { location; parameter_sort = Option.None; _ } ->
      raise @@ Illegal_untyped_pi_kind location
    | Synprs.LF.Object.RawType { location } ->
      Synext'.LF.Kind.Typ { location }
    | Synprs.LF.Object.RawForwardArrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_kind dictionary range in
      Synext'.LF.Kind.Arrow { location; domain = domain'; range = range' }
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } ->
      let parameter_type' = elaborate_typ dictionary parameter_type in
      let body' =
        match parameter_identifier with
        | Option.None -> elaborate_kind dictionary body
        | Option.Some identifier ->
          let dictionary' = Dictionary.add_term identifier dictionary in
          elaborate_kind dictionary' body
      in
      Synext'.LF.Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let kind = elaborate_kind dictionary object_ in
      Synext'.LF.Kind.Parenthesized { location; kind }

  and elaborate_typ dictionary object_ =
    match object_ with
    | Synprs.LF.Object.RawType { location; _ } ->
      raise @@ Illegal_type_kind_type location
    | Synprs.LF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_type location
    | Synprs.LF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_type location
    | Synprs.LF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_type location
    | Synprs.LF.Object.RawPi { location; parameter_sort = Option.None; _ } ->
      raise @@ Illegal_untyped_pi_type location
    | Synprs.LF.Object.RawIdentifier { location; identifier } -> (
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Dictionary.lookup qualified_identifier dictionary with
      | Option.Some (Dictionary.LF_type_constant _) ->
        Synext'.LF.Typ.Constant
          { location; identifier = qualified_identifier }
      | Option.Some entry -> raise @@ Expected_type_constant (location, entry)
      | Option.None ->
        raise @@ Unbound_type_constant (location, qualified_identifier))
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      match Dictionary.lookup identifier dictionary with
      | Option.Some (Dictionary.LF_type_constant _) ->
        Synext'.LF.Typ.Constant { location; identifier }
      | Option.Some entry -> raise @@ Expected_type_constant (location, entry)
      | Option.None -> raise @@ Unbound_type_constant (location, identifier))
    | Synprs.LF.Object.RawForwardArrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_typ dictionary range in
      Synext'.LF.Typ.ForwardArrow
        { location; domain = domain'; range = range' }
    | Synprs.LF.Object.RawBackwardArrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_typ dictionary range in
      Synext'.LF.Typ.BackwardArrow
        { location; domain = domain'; range = range' }
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
      let parameter_type' = elaborate_typ dictionary parameter_type in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_typ dictionary body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some parameter ->
        let dictionary' = Dictionary.add_term parameter dictionary in
        let body' = elaborate_typ dictionary' body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawApplication { location; objects } -> (
      match elaborate_application dictionary (List2.to_list objects) with
      | `Term term -> raise @@ Expected_type term
      | `Typ typ -> typ)
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let typ = elaborate_typ dictionary object_ in
      Synext'.LF.Typ.Parenthesized { location; typ }

  and elaborate_term dictionary object_ =
    match object_ with
    | Synprs.LF.Object.RawType { location; _ } ->
      raise @@ Illegal_type_kind_term location
    | Synprs.LF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term location
    | Synprs.LF.Object.RawForwardArrow { location; _ } ->
      raise @@ Illegal_forward_arrow_term location
    | Synprs.LF.Object.RawBackwardArrow { location; _ } ->
      raise @@ Illegal_backward_arrow_term location
    | Synprs.LF.Object.RawIdentifier { location; identifier } -> (
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Dictionary.lookup qualified_identifier dictionary with
      | Option.Some (Dictionary.LF_term_constant _) ->
        Synext'.LF.Term.Constant
          { location; identifier = qualified_identifier }
      | Option.Some Dictionary.LF_term ->
        Synext'.LF.Term.Variable { location; identifier }
      | Option.Some entry -> raise @@ Expected_term_constant (location, entry)
      | Option.None -> Synext'.LF.Term.Variable { location; identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      match Dictionary.lookup identifier dictionary with
      | Option.Some (Dictionary.LF_term_constant _) ->
        Synext'.LF.Term.Constant { location; identifier }
      | Option.Some entry -> raise @@ Expected_term_constant (location, entry)
      | Option.None -> raise @@ Unbound_term_constant (location, identifier))
    | Synprs.LF.Object.RawApplication { location; objects } -> (
      match elaborate_application dictionary (List2.to_list objects) with
      | `Typ typ -> raise @@ Expected_term typ
      | `Term term -> term)
    | Synprs.LF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (elaborate_typ dictionary) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_term dictionary body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let dictionary' = Dictionary.add_term name dictionary in
        let body' = elaborate_term dictionary' body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawHole { location } ->
      Synext'.LF.Term.Wildcard { location }
    | Synprs.LF.Object.RawAnnotated { location; object_; sort } ->
      let term = elaborate_term dictionary object_
      and typ = elaborate_typ dictionary sort in
      Synext'.LF.Term.TypeAnnotated { location; term; typ }
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let term = elaborate_term dictionary object_ in
      Synext'.LF.Term.Parenthesized { location; term }

  and elaborate_application dictionary =
    let module LF_operand = struct
      type t =
        | External_typ of Synext'.LF.Typ.t
        | External_term of Synext'.LF.Term.t
        | Parser_object of Synprs.LF.Object.t

      let location = function
        | External_typ t -> Synext'.LF.location_of_typ t
        | External_term t -> Synext'.LF.location_of_term t
        | Parser_object t -> Synprs.LF.location_of_object t
    end in
    let module LF_operator = struct
      type t =
        | Type_constant of
            { operator : Operator.t
            ; applicand : Synext'.LF.Typ.t
            }
        | Term_constant of
            { operator : Operator.t
            ; applicand : Synext'.LF.Term.t
            }

      let operator = function
        | Type_constant { operator; _ } | Term_constant { operator; _ } ->
          operator

      let arity = Fun.(operator >> Operator.arity)

      let precedence = Fun.(operator >> Operator.precedence)

      let fixity = Fun.(operator >> Operator.fixity)

      let associativity = Fun.(operator >> Operator.associativity)

      let location operator =
        match operator with
        | Type_constant { applicand; _ } ->
          Synext'.LF.location_of_typ applicand
        | Term_constant { applicand; _ } ->
          Synext'.LF.location_of_term applicand

      include (
        (val Eq.contramap (module Operator) operator) :
          Eq.EQ with type t := t)
    end in
    let module ShuntingYard =
      ShuntingYard.Make (LF_operand) (LF_operator)
        (struct
          let elaborate_arguments arguments =
            List.map
              (fun argument ->
                match argument with
                | LF_operand.External_term term -> term
                | LF_operand.External_typ typ -> raise @@ Expected_term typ
                | LF_operand.Parser_object object_ ->
                  elaborate_term dictionary object_)
              arguments

          let write operator arguments =
            let operator_location = LF_operator.location operator in
            let location =
              List.fold_left
                (fun acc t -> Location.join acc (LF_operand.location t))
                operator_location arguments
            in
            let arguments = elaborate_arguments arguments in
            match operator with
            | LF_operator.Type_constant { applicand; _ } ->
              LF_operand.External_typ
                (Synext'.LF.Typ.Application
                   { location; applicand; arguments })
            | LF_operator.Term_constant { applicand; _ } ->
              LF_operand.External_term
                (Synext'.LF.Term.Application
                   { location; applicand; arguments })
        end)
    in
    let identify_operators dictionary terms =
      let resolve_qualified_identifier identifier term =
        match Dictionary.lookup identifier dictionary with
        | Option.Some (Dictionary.LF_type_constant operator) ->
          let type' = elaborate_typ dictionary term in
          ShuntingYard.operator
            (LF_operator.Type_constant { operator; applicand = type' })
        | Option.Some (Dictionary.LF_term_constant operator) ->
          let term' = elaborate_term dictionary term in
          ShuntingYard.operator
            (LF_operator.Term_constant { operator; applicand = term' })
        | Option.Some _ | Option.None ->
          ShuntingYard.operand (LF_operand.Parser_object term)
      in
      let resolve_qualified_identifier_as_prefix identifier term =
        match Dictionary.lookup identifier dictionary with
        | Option.Some (Dictionary.LF_type_constant operator) ->
          let type' = elaborate_typ dictionary term in
          let operator' = Operator.as_prefix operator in
          ShuntingYard.operator
            (LF_operator.Type_constant
               { operator = operator'; applicand = type' })
        | Option.Some (Dictionary.LF_term_constant operator) ->
          let term' = elaborate_term dictionary term in
          let operator' = Operator.as_prefix operator in
          ShuntingYard.operator
            (LF_operator.Term_constant
               { operator = operator'; applicand = term' })
        | Option.Some _ | Option.None ->
          ShuntingYard.operand (LF_operand.Parser_object term)
      in
      let identify_operator term =
        let rec identify_operator_with_quoting nested =
          match nested with
          | Synprs.LF.Object.RawIdentifier { identifier; _ } ->
            let qualified_identifier =
              QualifiedIdentifier.make_simple identifier
            in
            resolve_qualified_identifier_as_prefix qualified_identifier term
          | Synprs.LF.Object.RawQualifiedIdentifier { identifier; _ } ->
            resolve_qualified_identifier_as_prefix identifier term
          | Synprs.LF.Object.RawParenthesized { object_; _ } ->
            identify_operator_with_quoting object_
          | _ -> ShuntingYard.operand (LF_operand.Parser_object term)
        in
        match term with
        | Synprs.LF.Object.RawIdentifier { identifier; _ } ->
          let qualified_identifier =
            QualifiedIdentifier.make_simple identifier
          in
          resolve_qualified_identifier qualified_identifier term
        | Synprs.LF.Object.RawQualifiedIdentifier { identifier; _ } ->
          resolve_qualified_identifier identifier term
        | Synprs.LF.Object.RawParenthesized { object_; _ } ->
          identify_operator_with_quoting object_
        | _ -> ShuntingYard.operand (LF_operand.Parser_object term)
      in
      List.map identify_operator terms
    in
    fun terms ->
      try
        match
          ShuntingYard.shunting_yard (identify_operators dictionary terms)
        with
        | LF_operand.External_typ t -> `Typ t
        | LF_operand.External_term t -> `Term t
        | LF_operand.Parser_object _ ->
          Error.violation
            "Unexpectedly did not elaborate LF operands in rewriting"
      with
      | ShuntingYard.Empty_expression -> raise @@ Empty_expression
      | ShuntingYard.Misplaced_operator (operator, operands) ->
        raise
        @@ Misplaced_operator
             ( LF_operator.location operator
             , List.map LF_operand.location operands )
      | ShuntingYard.Consecutive_non_associative_operators (o1, o2) ->
        raise
        @@ Consecutive_non_associative_operators
             (LF_operator.location o1, LF_operator.location o2)
      | ShuntingYard.Arity_mismatch (operator, operands) ->
        raise
        @@ Arity_mismatch
             ( LF_operator.location operator
             , List.map LF_operand.location operands )
      | ShuntingYard.Leftover_expressions expressions ->
        raise
        @@ Leftover_expressions (List2.map LF_operand.location expressions)
end
