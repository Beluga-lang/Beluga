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
    identifier:QualifiedIdentifier.t -> precedence:Int.t -> t

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

  let make_postfix ~identifier ~precedence =
    { identifier
    ; arity = 1
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
    precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_prefix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_infix_lf_term_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> QualifiedIdentifier.t
    -> t
    -> t

  val add_postfix_lf_term_constant :
    precedence:Int.t -> QualifiedIdentifier.t -> t -> t

  val add_module : t -> QualifiedIdentifier.t -> t -> t

  (** {1 Lookup} *)

  exception Unbound_identifier of QualifiedIdentifier.t

  exception Unbound_module of QualifiedIdentifier.t

  exception
    Expected_module of
      { identifier : QualifiedIdentifier.t
      ; actual_binding : entry
      }

  (** [lookup identifier dictionary] looks up [identifier] in [dictionary].

      @raise Unbound_identifier if [identifier] is unbound in [dictionary].
      @raise Unbound_module
        if a sub-part of [identifier] is unbound in [dictionary], for
        instance if module [Util::Nat] is unbound when looking up
        [Util::Nat::zero]
      @raise Expected_module
        if a sub-part of [identifier] is bound in [dictionary], but does not
        refer to a module *)
  val lookup : QualifiedIdentifier.t -> t -> entry

  (** {1 Interoperability} *)

  (** [to_seq dictionary] is [dictionary] flattened to a sequence of bindings
      by qualified name. There is no guarantee on the order of bindings in
      the resultant sequence. *)
  val to_seq : t -> (QualifiedIdentifier.t * entry) Seq.t

  (** {1 Error-Reporting} *)

  val pp_entry_sort : Format.formatter -> entry -> Unit.t
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

  let add_postfix_lf_type_constant ~precedence identifier =
    add_nested_entry
      (LF_type_constant (Operator.make_postfix ~identifier ~precedence))
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

  let add_postfix_lf_term_constant ~precedence identifier =
    add_nested_entry
      (LF_term_constant (Operator.make_postfix ~identifier ~precedence))
      identifier

  let add_module module_dictionary identifier =
    add_nested_entry (Module module_dictionary) identifier

  let pp_entry_sort ppf entry =
    match entry with
    | LF_term -> Format.fprintf ppf "an LF term"
    | LF_type_constant _ -> Format.fprintf ppf "an LF type-level constant"
    | LF_term_constant _ -> Format.fprintf ppf "an LF term-level constant"
    | Module _ -> Format.fprintf ppf "a module"

  exception Unbound_identifier of QualifiedIdentifier.t

  exception Unbound_module of QualifiedIdentifier.t

  exception
    Expected_module of
      { identifier : QualifiedIdentifier.t
      ; actual_binding : entry
      }

  let pp_exception ppf = function
    | Unbound_identifier identifier ->
      Format.fprintf ppf "Identifier \"%a\" is unbound: %a"
        QualifiedIdentifier.pp identifier Location.pp
        (QualifiedIdentifier.location identifier)
    | Unbound_module identifier ->
      Format.fprintf ppf "Module \"%a\" is unbound: %a"
        QualifiedIdentifier.pp identifier Location.pp
        (QualifiedIdentifier.location identifier)
    | Expected_module { identifier; actual_binding } ->
      Format.fprintf ppf
        "Expected \"%a\" to be a module but found %a instead: %a@."
        QualifiedIdentifier.pp identifier pp_entry_sort actual_binding
        Location.pp
        (QualifiedIdentifier.location identifier)
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.asprintf "%a" pp_exception exn
        with Invalid_argument _ -> Option.none)

  let lookup query dictionary =
    let rec lookup modules_to_lookup modules_looked_up_so_far dictionary =
      match modules_to_lookup with
      | [] (* Toplevel declaration *) -> (
        let name = QualifiedIdentifier.name query in
        match Identifier.Hamt.find_opt name dictionary with
        | Option.Some entry -> entry
        | Option.None -> raise @@ Unbound_identifier query)
      | m :: ms (* Nested declaration *) -> (
        let recover_current_module_identifier () =
          let location =
            List.fold_left
              (fun acc i -> Location.join acc (Identifier.location i))
              (Identifier.location m) modules_looked_up_so_far
          in
          QualifiedIdentifier.make ~location
            ~modules:(List.rev modules_looked_up_so_far)
            m
        in
        match Identifier.Hamt.find_opt m dictionary with
        | Option.Some (Module dictionary') ->
          lookup ms (m :: modules_looked_up_so_far) dictionary'
        | Option.Some actual_binding ->
          raise
          @@ Expected_module
               { identifier = recover_current_module_identifier ()
               ; actual_binding
               }
        | Option.None ->
          raise @@ Unbound_module (recover_current_module_identifier ()))
    in
    let modules = QualifiedIdentifier.modules query in
    lookup modules [] dictionary

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

module LF = struct
  (** {1 Exceptions} *)

  (** {2 Exceptions for LF kind elaboration} *)

  exception Illegal_identifier_kind of Location.t

  exception Illegal_qualified_identifier_kind of Location.t

  exception Illegal_backward_arrow_kind of Location.t

  exception Illegal_hole_kind of Location.t

  exception Illegal_lambda_kind of Location.t

  exception Illegal_annotated_kind of Location.t

  exception Illegal_application_kind of Location.t

  exception Illegal_untyped_pi_kind of Location.t

  (** {2 Exceptions for LF type elaboration} *)

  exception Illegal_type_kind_type of Location.t

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for LF term elaboration} *)

  exception Illegal_type_kind_term of Location.t

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding : Dictionary.entry
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding : Dictionary.entry
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception
    Misplaced_operator of
      { operator_location : Location.t
      ; operand_locations : Location.t List.t
      }

  exception
    Consecutive_non_associative_operators of
      { operator_identifier : QualifiedIdentifier.t
      ; left_operator_location : Location.t
      ; right_operator_location : Location.t
      }

  exception
    Arity_mismatch of
      { operator_identifier : QualifiedIdentifier.t
      ; operator_location : Location.t
      ; operator_arity : Int.t
      ; actual_argument_locations : Location.t List.t
      }

  exception Too_many_arguments of Location.t

  (** {2 Exception Printing} *)

  let pp_exception ppf = function
    | Illegal_identifier_kind location ->
      Format.fprintf ppf "Identifiers may not appear in LF kinds: %a@."
        Location.pp location
    | Illegal_qualified_identifier_kind location ->
      Format.fprintf ppf
        "Qualified identifiers may not appear in LF kinds: %a@." Location.pp
        location
    | Illegal_backward_arrow_kind location ->
      Format.fprintf ppf "Backward arrows may not appear in LF kinds: %a@."
        Location.pp location
    | Illegal_hole_kind location ->
      Format.fprintf ppf "Holes may not appear in LF kinds: %a@." Location.pp
        location
    | Illegal_lambda_kind location ->
      Format.fprintf ppf "Lambdas may not appear in LF kinds: %a@."
        Location.pp location
    | Illegal_annotated_kind location ->
      Format.fprintf ppf "Type ascriptions may not appear in LF kinds: %a@."
        Location.pp location
    | Illegal_application_kind location ->
      Format.fprintf ppf "Term applications may not appear in LF kinds: %a@."
        Location.pp location
    | Illegal_untyped_pi_kind location ->
      Format.fprintf ppf
        "The LF Pi kind is missing its parameter type annotation: %a@."
        Location.pp location
    | Illegal_type_kind_type location ->
      Format.fprintf ppf "The kind `type' may not appear in LF types: %a@."
        Location.pp location
    | Illegal_hole_type location ->
      Format.fprintf ppf "Holes may not appear in LF types: %a@." Location.pp
        location
    | Illegal_lambda_type location ->
      Format.fprintf ppf "Lambdas may not appear in LF types: %a@."
        Location.pp location
    | Illegal_annotated_type location ->
      Format.fprintf ppf "Type ascriptions may not appear in LF types: %a@."
        Location.pp location
    | Illegal_untyped_pi_type location ->
      Format.fprintf ppf
        "The LF Pi type is missing its parameter type annotation: %a@."
        Location.pp location
    | Unbound_type_constant { location; identifier } ->
      Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_type_kind_term location ->
      Format.fprintf ppf "The kind `type' may not appear in LF terms: %a@."
        Location.pp location
    | Illegal_pi_term location ->
      Format.fprintf ppf "Pi kinds or types may not appear in LF terms: %a@."
        Location.pp location
    | Illegal_forward_arrow_term location ->
      Format.fprintf ppf "Forward arrows may not appear in LF terms: %a@."
        Location.pp location
    | Illegal_backward_arrow_term location ->
      Format.fprintf ppf "Backward arrows may not appear in LF terms: %a@."
        Location.pp location
    | Unbound_term_constant { location; identifier } ->
      Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Expected_term_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found %a instead: %a@."
        Dictionary.pp_entry_sort actual_binding Location.pp location
    | Expected_type_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found %a instead: %a@."
        Dictionary.pp_entry_sort actual_binding Location.pp location
    | Expected_term location ->
      Format.fprintf ppf
        "Expected an LF term but found an LF type instead: %a@." Location.pp
        location
    | Misplaced_operator { operator_location; _ } ->
      Format.fprintf ppf
        "Misplaced LF term-level or type-level operator: %a@." Location.pp
        operator_location
    | Consecutive_non_associative_operators
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Consecutive occurrences of the LF term-level or type-level \
         operator %a after rewriting: %a and %a@."
        QualifiedIdentifier.pp operator_identifier Location.pp
        left_operator_location Location.pp right_operator_location
    | Arity_mismatch
        { operator_identifier
        ; operator_location
        ; operator_arity
        ; actual_argument_locations
        } ->
      let expected_arguments_count = operator_arity
      and actual_arguments_count = List.length actual_argument_locations in
      Format.fprintf ppf "Operator %a expected %d arguments but got %d: %a@."
        QualifiedIdentifier.pp operator_identifier expected_arguments_count
        actual_arguments_count Location.pp operator_location
    | Too_many_arguments location ->
      Format.fprintf ppf
        "Too many arguments are supplied to an operator: %a@." Location.pp
        location
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.asprintf "%a" pp_exception exn
        with Invalid_argument _ -> Option.none)

  (** {1 Elaboration} *)

  let resolve_lf_operator dictionary ~quoted identifier =
    match Dictionary.lookup identifier dictionary with
    | Dictionary.LF_type_constant operator ->
      if quoted then `Quoted_type_operator else `Type_operator operator
    | Dictionary.LF_term_constant operator ->
      if quoted then `Quoted_term_operator else `Term_operator operator
    | _ | (exception Dictionary.Unbound_identifier _) -> `Not_an_operator

  let rec identify_lf_operator dictionary ~quoted term =
    match term with
    | Synprs.LF.Object.RawIdentifier { identifier; _ } ->
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      resolve_lf_operator dictionary ~quoted qualified_identifier
    | Synprs.LF.Object.RawQualifiedIdentifier { identifier; _ } ->
      resolve_lf_operator dictionary ~quoted identifier
    | Synprs.LF.Object.RawParenthesized { object_; _ } ->
      identify_lf_operator dictionary ~quoted:true object_
    | _ -> `Not_an_operator

  module LF_operand = struct
    type t =
      | External_typ of Synext'.LF.Typ.t
      | External_term of Synext'.LF.Term.t
      | Parser_object of Synprs.LF.Object.t
      | Application of
          { applicand :
              [ `Typ of Synprs.LF.Object.t | `Term of Synprs.LF.Object.t ]
          ; arguments : Synprs.LF.Object.t List.t
          }

    let location = function
      | External_typ t -> Synext'.LF.location_of_typ t
      | External_term t -> Synext'.LF.location_of_term t
      | Parser_object t -> Synprs.LF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ applicand | `Term applicand ->
            Synprs.LF.location_of_object applicand
        in
        List.fold_left
          (fun acc a -> Location.join acc (Synprs.LF.location_of_object a))
          applicand_location arguments
  end

  module LF_operator = struct
    type t =
      | Type_constant of
          { operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }
      | Term_constant of
          { operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let identifier = Fun.(operator >> Operator.identifier)

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.LF.location_of_object)

    include (
      (val Eq.contramap (module Operator) operator) : Eq.EQ with type t := t)
  end

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
      | Dictionary.LF_type_constant _ ->
        Synext'.LF.Typ.Constant
          { location; identifier = qualified_identifier }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception Dictionary.Unbound_identifier _ ->
        raise
        @@ Unbound_type_constant
             { location; identifier = qualified_identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      match Dictionary.lookup identifier dictionary with
      | Dictionary.LF_type_constant _ ->
        Synext'.LF.Typ.Constant { location; identifier }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
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
      match elaborate_application dictionary objects with
      | `Term term ->
        let location = Synext'.LF.location_of_term term in
        raise @@ Expected_type location
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
      | Dictionary.LF_term_constant _ ->
        Synext'.LF.Term.Constant
          { location; identifier = qualified_identifier }
      | Dictionary.LF_term ->
        Synext'.LF.Term.Variable { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception Dictionary.Unbound_identifier _ ->
        Synext'.LF.Term.Variable { location; identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      match Dictionary.lookup identifier dictionary with
      | Dictionary.LF_term_constant _ ->
        Synext'.LF.Term.Constant { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.LF.Object.RawApplication { location; objects } -> (
      match elaborate_application dictionary objects with
      | `Typ typ ->
        let location = Synext'.LF.location_of_typ typ in
        raise @@ Expected_term location
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
    let elaborate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term applicand | `Typ applicand ->
          Synprs.LF.location_of_object applicand
      in
      let application_location =
        List.fold_left
          (fun acc operand ->
            Location.join acc (Synprs.LF.location_of_object operand))
          applicand_location arguments
      in
      match applicand with
      | `Term applicand ->
        let applicand' = elaborate_term dictionary applicand in
        let arguments' = List.map (elaborate_term dictionary) arguments in
        `Term
          (Synext'.LF.Term.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = elaborate_typ dictionary applicand in
        let arguments' = List.map (elaborate_term dictionary) arguments in
        `Typ
          (Synext'.LF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module ShuntingYard =
      ShuntingYard.Make (LF_operand) (LF_operator)
        (struct
          let elaborate_argument argument =
            match argument with
            | LF_operand.External_term term -> term
            | LF_operand.External_typ typ ->
              let location = Synext'.LF.location_of_typ typ in
              raise @@ Expected_term location
            | LF_operand.Parser_object object_ ->
              elaborate_term dictionary object_
            | LF_operand.Application { applicand; arguments } -> (
              match elaborate_juxtaposition applicand arguments with
              | `Term term -> term
              | `Typ typ ->
                let location = Synext'.LF.location_of_typ typ in
                raise @@ Expected_term location)

          let elaborate_arguments arguments =
            List.map elaborate_argument arguments

          let write operator arguments =
            let application_location =
              List.fold_left
                (fun acc operand ->
                  Location.join acc (LF_operand.location operand))
                (LF_operator.location operator)
                arguments
            in
            match operator with
            | LF_operator.Type_constant { applicand; _ } ->
              let applicand' = elaborate_typ dictionary applicand in
              let arguments' = elaborate_arguments arguments in
              LF_operand.External_typ
                (Synext'.LF.Typ.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
            | LF_operator.Term_constant { applicand; _ } ->
              let applicand' = elaborate_term dictionary applicand in
              let arguments' = elaborate_arguments arguments in
              LF_operand.External_term
                (Synext'.LF.Term.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
        end)
    in
    let prepare_terms terms =
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ -> true
        | `Type_operator _, _ | `Term_operator _, _ -> false
      in
      let rec reduce_juxtapositions_and_identify_operators terms =
        match terms with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (LF_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (LF_operand.Application
               { applicand = `Typ t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (LF_operand.Application
               { applicand = `Term t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator operator, t) :: ts ->
          ShuntingYard.operator
            (LF_operator.Type_constant { operator; applicand = t })
          :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator operator, t) :: ts ->
          ShuntingYard.operator
            (LF_operator.Term_constant { operator; applicand = t })
          :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      let terms =
        List2.map
          (fun term ->
            let tag = identify_lf_operator dictionary ~quoted:false term in
            (tag, term))
          terms
      in
      reduce_juxtapositions_and_identify_operators (List2.to_list terms)
    in
    fun terms ->
      try
        match ShuntingYard.shunting_yard (prepare_terms terms) with
        | LF_operand.External_typ t -> `Typ t
        | LF_operand.External_term t -> `Term t
        | LF_operand.Application { applicand; arguments } ->
          elaborate_juxtaposition applicand arguments
        | LF_operand.Parser_object _ ->
          Error.violation
            "[LF.elaborate_application] unexpectedly did not elaborate LF \
             operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[LF.elaborate_application] unexpectedly ended with an empty \
           expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[LF.elaborate_application] unexpectedly ended with leftover \
           expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = LF_operator.location operator
        and operand_locations = List.map LF_operand.location operands in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier = LF_operator.identifier left_operator
        and left_operator_location = LF_operator.location left_operator
        and right_operator_location = LF_operator.location right_operator in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = LF_operator.identifier operator
        and operator_location = LF_operator.location operator
        and actual_argument_locations =
          List.map LF_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }
end
