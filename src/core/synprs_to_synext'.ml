open Support

module Operator : sig
  type t

  (** {1 Destructors} *)

  val arity : t -> Int.t

  val precedence : t -> Int.t

  val fixity : t -> Fixity.t

  val associativity : t -> Associativity.t

  val location : t -> Location.t

  (** {1 Constructors} *)

  val make_prefix_operator :
    identifier:Identifier.t -> arity:Int.t -> precedence:Int.t -> t

  val make_infix_operator :
       identifier:Identifier.t
    -> associativity:Associativity.t
    -> precedence:Int.t
    -> t

  val make_postfix_operator :
    identifier:Identifier.t -> arity:Int.t -> precedence:Int.t -> t

  (** {1 Instances} *)

  include Eq.EQ with type t := t
end = struct
  type t =
    { identifier : Identifier.t
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

  let[@inline] location { identifier; _ } = Identifier.location identifier

  let make_prefix_operator ~identifier ~arity ~precedence =
    { identifier
    ; arity
    ; precedence
    ; fixity = Fixity.prefix
    ; associativity = Associativity.right_associative
    }

  let make_infix_operator ~identifier ~associativity ~precedence =
    { identifier
    ; arity = 2
    ; precedence
    ; fixity = Fixity.infix
    ; associativity
    }

  let make_postfix_operator ~identifier ~arity ~precedence =
    { identifier
    ; arity
    ; precedence
    ; fixity = Fixity.postfix
    ; associativity = Associativity.left_associative
    }

  include (
    (val Eq.contramap (module Identifier) identifier) :
      Eq.EQ with type t := t)
end

module Dictionary : sig
  type t

  type entry = private
    | LF_type
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | Module of t

  (** {1 Constructors} *)

  val empty : t

  val add_type : Identifier.t -> t -> t

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
end = struct
  type t = entry Identifier.Hamt.t

  and entry =
    | LF_type
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t
    | Module of t

  let empty = Identifier.Hamt.empty

  let add_entry entry identifier dictionary =
    Identifier.Hamt.add identifier entry dictionary

  let add_nested_entry entry qualified_identifier dictionary =
    let name = QualifiedIdentifier.name qualified_identifier
    and module_identifiers =
      QualifiedIdentifier.modules qualified_identifier
    in
    match module_identifiers with
    | [] -> add_entry entry name dictionary
    | m :: ms ->
      let rec add module_to_lookup next_modules dictionary =
        match Identifier.Hamt.find_opt module_to_lookup dictionary with
        | Option.Some (Module dictionary') -> (
          match next_modules with
          | [] ->
            Identifier.Hamt.update name
              (Fun.const Option.some entry)
              dictionary'
          | m :: ms ->
            Identifier.Hamt.update module_to_lookup
              (Fun.const Option.some @@ Module (add m ms dictionary'))
              dictionary)
        | Option.None ->
          Identifier.Hamt.add module_to_lookup
            (Module (add m ms empty))
            dictionary
        | Option.Some _ ->
          Identifier.Hamt.update module_to_lookup
            (Fun.const Option.some @@ Module (add m ms empty))
            dictionary
      in
      add m ms dictionary

  let add_type = add_entry LF_type

  let add_term = add_entry LF_term

  let add_prefix_lf_type_constant ~arity ~precedence qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_type_constant
         (Operator.make_prefix_operator ~identifier ~arity ~precedence))
      qualified_identifier

  let add_infix_lf_type_constant ~associativity ~precedence
      qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_type_constant
         (Operator.make_infix_operator ~identifier ~associativity ~precedence))
      qualified_identifier

  let add_postfix_lf_type_constant ~arity ~precedence qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_type_constant
         (Operator.make_postfix_operator ~identifier ~arity ~precedence))
      qualified_identifier

  let add_prefix_lf_term_constant ~arity ~precedence qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_term_constant
         (Operator.make_prefix_operator ~identifier ~arity ~precedence))
      qualified_identifier

  let add_infix_lf_term_constant ~associativity ~precedence
      qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_term_constant
         (Operator.make_infix_operator ~identifier ~associativity ~precedence))
      qualified_identifier

  let add_postfix_lf_term_constant ~arity ~precedence qualified_identifier =
    let identifier = QualifiedIdentifier.name qualified_identifier in
    add_nested_entry
      (LF_term_constant
         (Operator.make_postfix_operator ~identifier ~arity ~precedence))
      qualified_identifier

  let add_module module_dictionary =
    add_nested_entry (Module module_dictionary)

  let lookup qualified_identifier dictionary =
    let name = QualifiedIdentifier.name qualified_identifier
    and module_identifiers =
      QualifiedIdentifier.modules qualified_identifier
    in
    let rec lookup modules dictionary =
      match modules with
      | [] -> Identifier.Hamt.find_opt name dictionary
      | m :: ms -> (
        match Identifier.Hamt.find_opt m dictionary with
        | Option.Some (Module dictionary') -> lookup ms dictionary'
        | Option.Some _ | Option.None -> Option.none)
    in
    lookup module_identifiers dictionary
end

exception Unbound_qualified_identifier of QualifiedIdentifier.t

module LF = struct
  module Operand = struct
    type t =
      | External_typ of Synext'.LF.Typ.t
      | External_term of Synext'.LF.Term.t
      | Parser_typ of Synprs.LF.Typ.t
      | Parser_term of Synprs.LF.Term.t
  end

  module ShuntingYard =
    ShuntingYard.Make (Operand) (Operator)
      (struct
        let write operator arguments = Obj.magic () (* TODO: *)
      end)

  (* TODO: Given a list of terms, resolve operators, then only the writer
     elaborates types and terms. *)

  let rec elaborate_kind dictionary kind =
    match kind with
    | Synprs.LF.Kind.Typ { location } -> Synext'.LF.Kind.Typ { location }
    | Synprs.LF.Kind.Arrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_kind dictionary range in
      Synext'.LF.Kind.Arrow { location; domain = domain'; range = range' }
    | Synprs.LF.Kind.Pi { location; parameter_name; parameter_type; range }
      ->
      let parameter_type' = elaborate_typ dictionary parameter_type in
      let range' =
        match parameter_name with
        | Option.None -> elaborate_kind dictionary range
        | Option.Some name ->
          let dictionary' = Dictionary.add_type name dictionary in
          elaborate_kind dictionary' range
      in
      Synext'.LF.Kind.Pi
        { location
        ; parameter_name
        ; parameter_type = parameter_type'
        ; range = range'
        }
    | Synprs.LF.Kind.Parenthesized { location; kind } ->
      let kind' = elaborate_kind dictionary kind in
      Synext'.LF.Kind.Parenthesized { location; kind = kind' }

  and elaborate_typ dictionary typ =
    match typ with
    | Synprs.LF.Typ.RawApplication { location; terms } ->
      Obj.magic () (* TODO: rewrite terms to a type application *)
    | Synprs.LF.Typ.ForwardArrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_typ dictionary range in
      Synext'.LF.Typ.ForwardArrow
        { location; domain = domain'; range = range' }
    | Synprs.LF.Typ.BackwardArrow { location; domain; range } ->
      let domain' = elaborate_typ dictionary domain
      and range' = elaborate_typ dictionary range in
      Synext'.LF.Typ.BackwardArrow
        { location; domain = domain'; range = range' }
    | Synprs.LF.Typ.Pi { location; parameter_name; parameter_type; range }
      -> (
      let parameter_type' = elaborate_typ dictionary parameter_type in
      match parameter_name with
      | Option.None ->
        let range' = elaborate_typ dictionary range in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_name
          ; parameter_type = parameter_type'
          ; range = range'
          }
      | Option.Some name ->
        let dictionary' = Dictionary.add_type name dictionary in
        let range' = elaborate_typ dictionary' range in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_name
          ; parameter_type = parameter_type'
          ; range = range'
          })
    | Synprs.LF.Typ.Parenthesized { location; typ } ->
      let typ' = elaborate_typ dictionary typ in
      Synext'.LF.Typ.Parenthesized { location; typ = typ' }

  and elaborate_term dictionary term =
    match term with
    | Synprs.LF.Term.RawName { location; name } -> (
      let qualified_name = QualifiedIdentifier.make_simple name in
      match Dictionary.lookup qualified_name dictionary with
      | Option.None | Option.Some Dictionary.LF_term ->
        Synext'.LF.Term.Variable { location; name }
      | Option.Some (Dictionary.LF_term_constant _) ->
        Synext'.LF.Term.Constant { location; name = qualified_name }
      | Option.Some _ -> Obj.magic () (* TODO: Type error *))
    | Synprs.LF.Term.RawQualifiedName { location; qualified_name } -> (
      match Dictionary.lookup qualified_name dictionary with
      | Option.None -> raise @@ Unbound_qualified_identifier qualified_name
      | Option.Some (Dictionary.LF_term_constant _) ->
        Synext'.LF.Term.Constant { location; name = qualified_name }
      | Option.Some _ -> Obj.magic () (* TODO: Type error *))
    | Synprs.LF.Term.RawApplication { location; terms } ->
      Obj.magic () (* TODO: rewrite terms to a term application *)
    | Synprs.LF.Term.Abstraction
        { location; parameter_name; parameter_type; body } -> (
      let parameter_type' =
        Option.map (elaborate_typ dictionary) parameter_type
      in
      match parameter_name with
      | Option.None ->
        let body' = elaborate_term dictionary body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_name
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let dictionary' = Dictionary.add_term name dictionary in
        let body' = elaborate_term dictionary' body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_name
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Term.Wildcard { location } ->
      Synext'.LF.Term.Wildcard { location }
    | Synprs.LF.Term.TypeAnnotated { location; term; typ } ->
      let term' = elaborate_term dictionary term
      and typ' = elaborate_typ dictionary typ in
      Synext'.LF.Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Synprs.LF.Term.Parenthesized { location; term } ->
      let term' = elaborate_term dictionary term in
      Synext'.LF.Term.Parenthesized { location; term = term' }
end
