open Support

module Elaboration_state : sig
  type t

  type entry = private
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t

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

  val lookup :
    QualifiedIdentifier.t -> t -> entry QualifiedIdentifier.Dictionary.value

  (** {1 Error-Reporting} *)

  val pp_entry_sort :
    Format.formatter -> entry QualifiedIdentifier.Dictionary.value -> Unit.t
end = struct
  type t = entry QualifiedIdentifier.Dictionary.t

  and entry =
    | LF_term
    | LF_type_constant of Operator.t
    | LF_term_constant of Operator.t

  let empty = QualifiedIdentifier.Dictionary.empty

  let add_term identifier =
    let qualified_identifier = QualifiedIdentifier.make_simple identifier in
    QualifiedIdentifier.Dictionary.add_entry qualified_identifier LF_term

  let add_prefix_lf_type_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_type_constant operator)

  let add_infix_lf_type_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_type_constant operator)

  let add_postfix_lf_type_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_type_constant operator)

  let add_prefix_lf_term_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_term_constant operator)

  let add_infix_lf_term_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_term_constant operator)

  let add_postfix_lf_term_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    QualifiedIdentifier.Dictionary.add_entry identifier
      (LF_term_constant operator)

  let add_module module_dictionary identifier =
    QualifiedIdentifier.Dictionary.add_module identifier module_dictionary

  let lookup query state = QualifiedIdentifier.Dictionary.lookup query state

  let pp_entry_sort ppf entry =
    match entry with
    | QualifiedIdentifier.Dictionary.Entry LF_term ->
      Format.fprintf ppf "an LF term"
    | QualifiedIdentifier.Dictionary.Entry (LF_type_constant _) ->
      Format.fprintf ppf "an LF type-level constant"
    | QualifiedIdentifier.Dictionary.Entry (LF_term_constant _) ->
      Format.fprintf ppf "an LF term-level constant"
    | QualifiedIdentifier.Dictionary.Module _ ->
      Format.fprintf ppf "a module"
end

(** Elaboration of LF kinds, types and terms from the parser syntax to the
    external syntax.

    This elaboration does not perform normalization nor validation. *)
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
      ; actual_binding :
          Elaboration_state.entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          Elaboration_state.entry QualifiedIdentifier.Dictionary.value
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
      Format.fprintf ppf "Identifiers may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_qualified_identifier_kind location ->
      Format.fprintf ppf
        "Qualified identifiers may not appear as LF kinds: %a@." Location.pp
        location
    | Illegal_backward_arrow_kind location ->
      Format.fprintf ppf "Backward arrows may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_hole_kind location ->
      Format.fprintf ppf "Holes may not appear as LF kinds: %a@." Location.pp
        location
    | Illegal_lambda_kind location ->
      Format.fprintf ppf "Lambdas may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_annotated_kind location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_application_kind location ->
      Format.fprintf ppf "Term applications may not appear as LF kinds: %a@."
        Location.pp location
    | Illegal_untyped_pi_kind location ->
      Format.fprintf ppf
        "The LF Pi kind is missing its parameter type annotation: %a@."
        Location.pp location
    | Illegal_type_kind_type location ->
      Format.fprintf ppf "The kind `type' may not appear as LF types: %a@."
        Location.pp location
    | Illegal_hole_type location ->
      Format.fprintf ppf "Holes may not appear as LF types: %a@." Location.pp
        location
    | Illegal_lambda_type location ->
      Format.fprintf ppf "Lambdas may not appear as LF types: %a@."
        Location.pp location
    | Illegal_annotated_type location ->
      Format.fprintf ppf "Type ascriptions may not appear as LF types: %a@."
        Location.pp location
    | Illegal_untyped_pi_type location ->
      Format.fprintf ppf
        "The LF Pi type is missing its parameter type annotation: %a@."
        Location.pp location
    | Unbound_type_constant { location; identifier } ->
      Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_type_kind_term location ->
      Format.fprintf ppf "The kind `type' may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_pi_term location ->
      Format.fprintf ppf "Pi kinds or types may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_forward_arrow_term location ->
      Format.fprintf ppf "Forward arrows may not appear as LF terms: %a@."
        Location.pp location
    | Illegal_backward_arrow_term location ->
      Format.fprintf ppf "Backward arrows may not appear as LF terms: %a@."
        Location.pp location
    | Unbound_term_constant { location; identifier } ->
      Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Expected_term_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found %a instead: %a@."
        Elaboration_state.pp_entry_sort actual_binding Location.pp location
    | Expected_type_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found %a instead: %a@."
        Elaboration_state.pp_entry_sort actual_binding Location.pp location
    | Expected_term location ->
      Format.fprintf ppf
        "Expected an LF term but found an LF type instead: %a@." Location.pp
        location
    | Expected_type location ->
      Format.fprintf ppf
        "Expected an LF type but found an LF term instead: %a@." Location.pp
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
        try Option.some @@ Format.stringify pp_exception exn
        with Invalid_argument _ -> Option.none)

  (** {1 Elaboration} *)

  (** [resolve_lf_operator state ~quoted identifier] determines whether
      [identifier] is an LF type-level or term-level operator in [state], and
      whether it is quoted. *)
  let resolve_lf_operator state ~quoted identifier =
    match Elaboration_state.lookup identifier state with
    | QualifiedIdentifier.Dictionary.Entry
        (Elaboration_state.LF_type_constant operator) ->
      if quoted then `Quoted_type_operator
      else `Type_operator (identifier, operator)
    | QualifiedIdentifier.Dictionary.Entry
        (Elaboration_state.LF_term_constant operator) ->
      if quoted then `Quoted_term_operator
      else `Term_operator (identifier, operator)
    | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _) ->
      `Not_an_operator

  (** [identifier_lf_operator state ?quoted term] identifies whether [term]
      is an LF type-level or term-level operator in [state] while accounting
      for operator quoting. If a bound operator appears in parentheses, then
      it is quoted, meaning that the operator appears either in prefix
      notation or as an argument to another application. *)
  let rec identify_lf_operator state ?(quoted = false) term =
    match term with
    | Synprs.LF.Object.RawIdentifier { identifier; _ } ->
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.LF.Object.RawQualifiedIdentifier { identifier; _ } ->
      resolve_lf_operator state ~quoted identifier
    | Synprs.LF.Object.RawParenthesized { object_; _ } ->
      identify_lf_operator state ~quoted:true object_
    | _ -> `Not_an_operator

  (** LF term-level or type-level operands for rewriting of prefix, infix and
      postfix operators using {!ShuntingYard}. *)
  module LF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext'.LF.Typ.t  (** An elaborated LF type. *)
      | External_term of Synext'.LF.Term.t  (** An elaborated LF term. *)
      | Parser_object of Synprs.LF.Object.t
          (** An LF object that has yet to be elaborated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.LF.Object.t | `Term of Synprs.LF.Object.t ]
          ; arguments : Synprs.LF.Object.t List.t
          }  (** An LF type-level or term-level application. *)

    (** {1 Destructors} *)

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

  (** LF term-level or type-level operators for rewriting of prefix, infix
      and postfix operators using {!ShuntingYard}. *)
  module LF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }
          (** An LF type-level constant with its operator definition in the
              elaboration context, and its corresponding AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.LF.Object.t
          }
          (** An LF term-level constant with its operator definition in the
              elaboration context, and its corresponding AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.LF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [elaborate_kind state object_] is [object_] rewritten as an LF kind
      with respect to the elaboration context [state].

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF kinds, see the Beluga language specification.

      Examples of invalid kinds that may result from this elaboration
      include:

      - [type -> type]
      - [(type -> type) -> type]
      - [{ x : tp } type -> type] *)
  let rec elaborate_kind state object_ =
    match object_ with
    | Synprs.LF.Object.RawIdentifier { location; _ } ->
      raise @@ Illegal_identifier_kind location
    | Synprs.LF.Object.RawQualifiedIdentifier { location; _ } ->
      raise @@ Illegal_qualified_identifier_kind location
    | Synprs.LF.Object.RawArrow { location; orientation = `Backward; _ } ->
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
    | Synprs.LF.Object.RawArrow
        { location; left_operand; right_operand; orientation = `Forward } ->
      let domain' = elaborate_typ state left_operand
      and range' = elaborate_kind state right_operand in
      Synext'.LF.Kind.Arrow { location; domain = domain'; range = range' }
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } ->
      let parameter_type' = elaborate_typ state parameter_type in
      let body' =
        match parameter_identifier with
        | Option.None -> elaborate_kind state body
        | Option.Some identifier ->
          let state' = Elaboration_state.add_term identifier state in
          elaborate_kind state' body
      in
      Synext'.LF.Kind.Pi
        { location
        ; parameter_identifier
        ; parameter_type = parameter_type'
        ; body = body'
        }
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let kind' = elaborate_kind state object_ in
      Synext'.LF.Kind.Parenthesized { location; kind = kind' }

  (** [elaborate_typ state object_] is [object_] rewritten as an LF type with
      respect to the elaboration context [state].

      Type applications are rewritten with {!elaborate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification.

      Examples of invalid types that may result from this elaboration
      include:

      - [c (_ _) _] *)
  and elaborate_typ state object_ =
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
      (* As an LF type, plain identifiers are necessarily type-level
         constants. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.LF.Typ.Constant
          { location; identifier = qualified_identifier; operator }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise
        @@ Unbound_type_constant
             { location; identifier = qualified_identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF type, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily type-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.LF.Typ.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
    | Synprs.LF.Object.RawArrow _ -> elaborate_arrows state object_
    | Synprs.LF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
      let parameter_type' = elaborate_typ state parameter_type in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_typ state body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some parameter ->
        let state' = Elaboration_state.add_term parameter state in
        let body' = elaborate_typ state' body in
        Synext'.LF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawApplication { objects; _ } -> (
      match elaborate_application state objects with
      | `Term term ->
        let location = Synext'.LF.location_of_term term in
        raise @@ Expected_type location
      | `Typ typ -> typ)
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let typ' = elaborate_typ state object_ in
      Synext'.LF.Typ.Parenthesized { location; typ = typ' }

  (** [elaborate_term state object_] is [object_] rewritten as an LF term
      with respect to the elaboration context [state].

      Term applications are rewritten with {!elaborate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid terms that may result from this elaboration
      include:

      - [_ _]
      - [\\_. _ _] *)
  and elaborate_term state object_ =
    match object_ with
    | Synprs.LF.Object.RawType { location; _ } ->
      raise @@ Illegal_type_kind_term location
    | Synprs.LF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term location
    | Synprs.LF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term location
    | Synprs.LF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term location
    | Synprs.LF.Object.RawIdentifier { location; identifier } -> (
      (* As an LF term, plain identifiers are either term-level constants or
         variables (bound or free). *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.LF.Term.Constant
          { location; identifier = qualified_identifier; operator }
      | QualifiedIdentifier.Dictionary.Entry Elaboration_state.LF_term ->
        (* Bound variable *)
        Synext'.LF.Term.Variable { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        (* Free variable *)
        Synext'.LF.Term.Variable { location; identifier })
    | Synprs.LF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.LF.Term.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.LF.Object.RawApplication { objects; _ } -> (
      match elaborate_application state objects with
      | `Typ typ ->
        let location = Synext'.LF.location_of_typ typ in
        raise @@ Expected_term location
      | `Term term -> term)
    | Synprs.LF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (elaborate_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_term state body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Elaboration_state.add_term name state in
        let body' = elaborate_term state' body in
        Synext'.LF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.LF.Object.RawHole { location } ->
      Synext'.LF.Term.Wildcard { location }
    | Synprs.LF.Object.RawAnnotated { location; object_; sort } ->
      let term' = elaborate_term state object_
      and typ' = elaborate_typ state sort in
      Synext'.LF.Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Synprs.LF.Object.RawParenthesized { location; object_ } ->
      let term' = elaborate_term state object_ in
      Synext'.LF.Term.Parenthesized { location; term = term' }

  (** [elaborate_arrows state arrow] elaborates the LF arrow type [arrow].
      Both forward and backward arrows were parsed as right-associative
      because the parser is top-down whereas bottom-up parsing is required to
      handle left and right-associative operators of the same precedence.

      This elaboration step uses Dijkstra's shunting yard algorithm in a
      simpler setting than that of {!elaborate_application}. *)
  and elaborate_arrows state =
    let module Arrow_operand = struct
      type t = Synext'.LF.Typ.t
    end in
    let module Arrow_operator = struct
      type t =
        | Forward_arrow
        | Backward_arrow

      let arity _ = 2

      let precedence _ = 0

      let fixity _ = Fixity.infix

      let associativity = function
        | Forward_arrow -> Associativity.right_associative
        | Backward_arrow -> Associativity.left_associative

      include (
        Eq.Make (struct
          type nonrec t = t

          let equal = Stdlib.( = )
        end) :
          Eq.EQ with type t := t)
    end in
    let module Arrow_writer = struct
      (** [write operator operands] writes the application of the forward or
          backward infix arrow [operator] with the two operands [operands]. *)
      let write operator operands =
        let[@warning "-8"] [ left_operand; right_operand ] = operands in
        let location =
          Location.join
            (Synext'.LF.location_of_typ left_operand)
            (Synext'.LF.location_of_typ right_operand)
        in
        match operator with
        | Arrow_operator.Forward_arrow ->
          Synext'.LF.Typ.ForwardArrow
            { location; domain = left_operand; range = right_operand }
        | Arrow_operator.Backward_arrow ->
          Synext'.LF.Typ.BackwardArrow
            { location; range = left_operand; domain = right_operand }
    end in
    let module ShuntingYard =
      ShuntingYard.Make (Arrow_operand) (Arrow_operator) (Arrow_writer)
    in
    (* [flatten object_] reduces the chain of parsed right-associative arrows
       to an alternating list of operands (elaborated LF types) and operators
       (either forward or backward arrows). *)
    let rec flatten object_ =
      match object_ with
      | Synprs.LF.Object.RawArrow
          { left_operand; right_operand; orientation = `Backward; _ } ->
        ShuntingYard.operand (elaborate_typ state left_operand)
        :: ShuntingYard.operator Arrow_operator.Backward_arrow
        :: flatten right_operand
      | Synprs.LF.Object.RawArrow
          { left_operand; right_operand; orientation = `Forward; _ } ->
        ShuntingYard.operand (elaborate_typ state left_operand)
        :: ShuntingYard.operator Arrow_operator.Forward_arrow
        :: flatten right_operand
      | _ -> [ ShuntingYard.operand (elaborate_typ state object_) ]
    in
    fun arrow -> ShuntingYard.shunting_yard (flatten arrow)

  (** [elaborate_application state objects] elaborates [objects] as either a
      type-level or term-level LF application with respect to the elaboration
      context [state].

      In both type-level and term-level LF applications, arguments are LF
      terms.

      This elaboration is in three steps:

      - First, LF type-level and term-level constants are identified as
        operators (with or without quoting) using [state], and the rest are
        identified as operands.
      - Second, consecutive operands are combined as an application
        (juxtaposition) that has yet to be elaborated, and written in prefix
        notation with the first operand being the application head.
      - Third, Dijkstra's shunting yard algorithm is used to rewrite the
        identified prefix, infix and postfix operators to applications. *)
  and elaborate_application state =
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
        let applicand' = elaborate_term state applicand in
        let arguments' = List.map (elaborate_term state) arguments in
        `Term
          (Synext'.LF.Term.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = elaborate_typ state applicand in
        let arguments' = List.map (elaborate_term state) arguments in
        `Typ
          (Synext'.LF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module LF_application_writer = struct
      (** [elaborate_argument argument] elaborates [argument] to an LF term.

          @raise Expected_term *)
      let elaborate_argument argument =
        match argument with
        | LF_operand.External_term term -> term
        | LF_operand.External_typ typ ->
          let location = Synext'.LF.location_of_typ typ in
          raise @@ Expected_term location
        | LF_operand.Parser_object object_ -> elaborate_term state object_
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
          let applicand' = elaborate_typ state applicand in
          let arguments' = elaborate_arguments arguments in
          LF_operand.External_typ
            (Synext'.LF.Typ.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
        | LF_operator.Term_constant { applicand; _ } ->
          let applicand' = elaborate_term state applicand in
          let arguments' = elaborate_arguments arguments in
          LF_operand.External_term
            (Synext'.LF.Term.Application
               { location = application_location
               ; applicand = applicand'
               ; arguments = arguments'
               })
    end in
    let module ShuntingYard =
      ShuntingYard.Make (LF_operand) (LF_operator) (LF_application_writer)
    in
    (* [prepare_objects objects] identifies operators in [objects] and
       rewrites juxtapositions to applications in prefix notation. The
       objects themselves are not elaborated to LF types or terms yet. This
       is only done in the shunting yard algorithm so that the leftmost
       syntax error gets reported. *)
    let prepare_objects objects =
      (* Predicate for identified objects that may appear as juxtaposed
         arguments to an application in prefix notation. This predicate does
         not apply to the application head. *)
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
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
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (LF_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (LF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (LF_operator.Term_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      objects |> List2.to_list
      |> List.map (fun term ->
             let tag = identify_lf_operator state term in
             (tag, term))
      |> reduce_juxtapositions_and_identify_operators
    in
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
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

(** Elaboration of contextual LF types, terms and patterns from the parser
    syntax to the external syntax.

    This elaboration does not perform normalization nor validation. *)
module CLF = struct
  (** {1 Exceptions} *)

  (** {2 Exceptions for contextual LF type elaboration} *)

  exception Illegal_hole_type of Location.t

  exception Illegal_lambda_type of Location.t

  exception Illegal_annotated_type of Location.t

  exception Illegal_untyped_pi_type of Location.t

  exception Illegal_tuple_type of Location.t

  exception Illegal_projection_type of Location.t

  exception Illegal_substitution_type of Location.t

  exception
    Unbound_type_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for contextual LF term elaboration} *)

  exception Illegal_pi_term of Location.t

  exception Illegal_forward_arrow_term of Location.t

  exception Illegal_backward_arrow_term of Location.t

  exception Illegal_block_term of Location.t

  exception
    Unbound_term_constant of
      { location : Location.t
      ; identifier : QualifiedIdentifier.t
      }

  (** {2 Exceptions for application rewriting} *)

  exception
    Expected_term_constant of
      { location : Location.t
      ; actual_binding :
          Elaboration_state.entry QualifiedIdentifier.Dictionary.value
      }

  exception
    Expected_type_constant of
      { location : Location.t
      ; actual_binding :
          Elaboration_state.entry QualifiedIdentifier.Dictionary.value
      }

  exception Expected_term of Location.t

  exception Expected_type of Location.t

  exception Expected_term_pattern of Location.t

  exception Expected_type_pattern of Location.t

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

  (** {2 Exceptions for contextual LF type pattern elaboration} *)

  exception Illegal_labellable_hole_type_pattern of Location.t

  exception Illegal_lambda_type_pattern of Location.t

  exception Illegal_annotated_type_pattern of Location.t

  exception Illegal_tuple_type_pattern of Location.t

  exception Illegal_projection_type_pattern of Location.t

  exception Illegal_substitution_type_pattern of Location.t

  exception Illegal_pi_type_pattern of Location.t

  exception Illegal_forward_arrow_type_pattern of Location.t

  exception Illegal_backward_arrow_type_pattern of Location.t

  (** {2 Exceptions for contextual LF term pattern elaboration} *)

  exception Illegal_pi_term_pattern of Location.t

  exception Illegal_forward_arrow_term_pattern of Location.t

  exception Illegal_backward_arrow_term_pattern of Location.t

  exception Illegal_block_term_pattern of Location.t

  exception Illegal_labellable_hole_term_pattern of Location.t

  (** {2 Exception Printing} *)

  let pp_exception ppf = function
    | Illegal_hole_type location ->
      Format.fprintf ppf "Holes may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_lambda_type location ->
      Format.fprintf ppf
        "Lambdas may not appear as contextual LF types: %a@." Location.pp
        location
    | Illegal_annotated_type location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF types: \
         %a@."
        Location.pp location
    | Illegal_untyped_pi_type location ->
      Format.fprintf ppf
        "The contextual LF Pi type is missing its parameter type \
         annotation: %a@."
        Location.pp location
    | Illegal_tuple_type location ->
      Format.fprintf ppf
        "Tuple terms may not appear as contextual LF types: %a@." Location.pp
        location
    | Illegal_projection_type location ->
      Format.fprintf ppf
        "Projection terms may not appear as contextual LF types: %a@."
        Location.pp location
    | Illegal_substitution_type location ->
      Format.fprintf ppf
        "Substitution terms may not appear as contextual LF types: %a@."
        Location.pp location
    | Unbound_type_constant { location; identifier } ->
      Format.fprintf ppf "The LF type-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Illegal_pi_term location ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_forward_arrow_term location ->
      Format.fprintf ppf
        "Forward arrows may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_backward_arrow_term location ->
      Format.fprintf ppf
        "Backward arrows may not appear as contextual LF terms: %a@."
        Location.pp location
    | Illegal_block_term location ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF terms: %a@." Location.pp
        location
    | Unbound_term_constant { location; identifier } ->
      Format.fprintf ppf "The LF term-level constant %a is unbound: %a@."
        QualifiedIdentifier.pp identifier Location.pp location
    | Expected_term_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF term-level constant but found %a instead: %a@."
        Elaboration_state.pp_entry_sort actual_binding Location.pp location
    | Expected_type_constant { location; actual_binding } ->
      Format.fprintf ppf
        "Expected an LF type-level constant but found %a instead: %a@."
        Elaboration_state.pp_entry_sort actual_binding Location.pp location
    | Expected_term location ->
      Format.fprintf ppf
        "Expected a contextual LF term but found a contextual LF type \
         instead: %a@."
        Location.pp location
    | Expected_type location ->
      Format.fprintf ppf
        "Expected an LF type but found an LF term instead: %a@." Location.pp
        location
    | Misplaced_operator { operator_location; _ } ->
      Format.fprintf ppf
        "Misplaced contextual LF term-level or type-level operator: %a@."
        Location.pp operator_location
    | Consecutive_non_associative_operators
        { operator_identifier
        ; left_operator_location
        ; right_operator_location
        } ->
      Format.fprintf ppf
        "Consecutive occurrences of the contextual LF term-level or \
         type-level operator %a after rewriting: %a and %a@."
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
    | Expected_term_pattern location ->
      Format.fprintf ppf
        "Expected a contextual LF term pattern but found a contextual LF \
         type pattern instead: %a@."
        Location.pp location
    | Expected_type_pattern location ->
      Format.fprintf ppf
        "Expected a contextual LF type pattern but found a contextual LF \
         term pattern instead: %a@."
        Location.pp location
    | Illegal_labellable_hole_type_pattern location ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_lambda_type_pattern location ->
      Format.fprintf ppf
        "Lambdas may not appear as contextual LF type patterns: %a@."
        Location.pp location
    | Illegal_annotated_type_pattern location ->
      Format.fprintf ppf
        "Type ascriptions to terms may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_tuple_type_pattern location ->
      Format.fprintf ppf
        "Tuple term patterns may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_projection_type_pattern location ->
      Format.fprintf ppf
        "Projection term patterns may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_substitution_type_pattern location ->
      Format.fprintf ppf
        "Substitution term patterns may not appear as contextual LF type \
         patterns: %a@."
        Location.pp location
    | Illegal_pi_type_pattern location ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_forward_arrow_type_pattern location ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_backward_arrow_type_pattern location ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF type patterns: \
         %a@."
        Location.pp location
    | Illegal_pi_term_pattern location ->
      Format.fprintf ppf
        "Pi kinds or types may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | Illegal_forward_arrow_term_pattern location ->
      Format.fprintf ppf
        "Forward arrow types may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | Illegal_backward_arrow_term_pattern location ->
      Format.fprintf ppf
        "Backward arrow types may not appear as contextual LF term \
         patterns: %a@."
        Location.pp location
    | Illegal_block_term_pattern location ->
      Format.fprintf ppf
        "Block types may not appear as contextual LF term patterns: %a@."
        Location.pp location
    | Illegal_labellable_hole_term_pattern location ->
      Format.fprintf ppf
        "Labellable holes may not appear as contextual LF term patterns: \
         %a@."
        Location.pp location
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.stringify pp_exception exn
        with Invalid_argument _ -> Option.none)

  (** {1 Elaboration} *)

  (** [resolve_lf_operator state ~quoted identifier] determines whether
      [identifier] is an LF type-level or term-level operator in [state], and
      whether it is quoted. *)
  let resolve_lf_operator state ~quoted identifier =
    match Elaboration_state.lookup identifier state with
    | QualifiedIdentifier.Dictionary.Entry
        (Elaboration_state.LF_type_constant operator) ->
      if quoted then `Quoted_type_operator
      else `Type_operator (identifier, operator)
    | QualifiedIdentifier.Dictionary.Entry
        (Elaboration_state.LF_term_constant operator) ->
      if quoted then `Quoted_term_operator
      else `Term_operator (identifier, operator)
    | _ | (exception QualifiedIdentifier.Dictionary.Unbound_identifier _) ->
      `Not_an_operator

  (** [identifier_lf_operator state ?quoted term] identifies whether [term]
      is an LF type-level or term-level operator in [state] while accounting
      for operator quoting. If a bound operator appears in parentheses, then
      it is quoted, meaning that the operator appears either in prefix
      notation or as an argument to another application. *)
  let rec identify_lf_operator state ?(quoted = false) term =
    match term with
    | Synprs.CLF.Object.RawIdentifier { identifier; _ } ->
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      resolve_lf_operator state ~quoted qualified_identifier
    | Synprs.CLF.Object.RawQualifiedIdentifier { identifier; _ } ->
      resolve_lf_operator state ~quoted identifier
    | Synprs.CLF.Object.RawParenthesized { object_; _ } ->
      identify_lf_operator state ~quoted:true object_
    | _ -> `Not_an_operator

  (** Contextual LF term-level or type-level operands for rewriting of
      prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ of Synext'.CLF.Typ.t
          (** An elaborated contextual LF type. *)
      | External_term of Synext'.CLF.Term.t
          (** An elaborated contextual LF term. *)
      | Parser_object of Synprs.CLF.Object.t
          (** A contextual LF object that has yet to be elaborated. *)
      | Application of
          { applicand :
              [ `Typ of Synprs.CLF.Object.t | `Term of Synprs.CLF.Object.t ]
          ; arguments : Synprs.CLF.Object.t List.t
          }  (** A contextual LF type-level or term-level application. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ t -> Synext'.CLF.location_of_typ t
      | External_term t -> Synext'.CLF.location_of_term t
      | Parser_object t -> Synprs.CLF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ applicand | `Term applicand ->
            Synprs.CLF.location_of_object applicand
        in
        List.fold_left
          (fun acc a -> Location.join acc (Synprs.CLF.location_of_object a))
          applicand_location arguments
  end

  (** Contextual LF term-level or type-level operators for rewriting of
      prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF type-level constant with its operator
              definition in the elaboration context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF term-level constant with its operator
              definition in the elaboration context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.CLF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [elaborate_typ state object_] is [object_] rewritten as a contextual LF
      type with respect to the elaboration context [state].

      Type applications are rewritten with {!elaborate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification.

      Examples of invalid types that may result from this elaboration
      include:

      - [c (_ _) _] *)
  let rec elaborate_typ state object_ =
    match object_ with
    | Synprs.CLF.Object.RawHole { location; _ } ->
      raise @@ Illegal_hole_type location
    | Synprs.CLF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_type location
    | Synprs.CLF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_type location
    | Synprs.CLF.Object.RawPi { location; parameter_sort = Option.None; _ }
      -> raise @@ Illegal_untyped_pi_type location
    | Synprs.CLF.Object.RawTuple { location; _ } ->
      raise @@ Illegal_tuple_type location
    | Synprs.CLF.Object.RawProjection { location; _ } ->
      raise @@ Illegal_projection_type location
    | Synprs.CLF.Object.RawSubstitution { location; _ } ->
      raise @@ Illegal_substitution_type location
    | Synprs.CLF.Object.RawIdentifier { location; identifier } -> (
      (* As an LF type, plain identifiers are necessarily type-level
         constants. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Constant
          { location; identifier = qualified_identifier; operator }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise
        @@ Unbound_type_constant
             { location; identifier = qualified_identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF type, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily type-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
    | Synprs.CLF.Object.RawArrow _ -> elaborate_arrows state object_
    | Synprs.CLF.Object.RawPi
        { location
        ; parameter_identifier
        ; parameter_sort = Option.Some parameter_type
        ; body
        } -> (
      let parameter_type' = elaborate_typ state parameter_type in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_typ state body in
        Synext'.CLF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some parameter ->
        let state' = Elaboration_state.add_term parameter state in
        let body' = elaborate_typ state' body in
        Synext'.CLF.Typ.Pi
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match elaborate_application state objects with
      | `Term term ->
        let location = Synext'.CLF.location_of_term term in
        raise @@ Expected_type location
      | `Typ typ -> typ)
    | Synprs.CLF.Object.RawBlock { location; elements = x, xs } ->
      let elements' =
        ( Pair.map_right (elaborate_typ state) x
        , List.map (Pair.map_right (elaborate_typ state)) xs )
      in
      Synext'.CLF.Typ.Block { location; elements = elements' }
    | Synprs.CLF.Object.RawParenthesized { location; object_ } ->
      let typ' = elaborate_typ state object_ in
      Synext'.CLF.Typ.Parenthesized { location; typ = typ' }

  (** [elaborate_term state object_] is [object_] rewritten as a contextual
      LF term with respect to the elaboration context [state].

      Term applications are rewritten with {!elaborate_application} using
      Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid terms that may result from this elaboration
      include:

      - [_ _]
      - [\\_. _ _] *)
  and elaborate_term state object_ =
    match object_ with
    | Synprs.CLF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term location
    | Synprs.CLF.Object.RawBlock { location; _ } ->
      raise @@ Illegal_block_term location
    | Synprs.CLF.Object.RawIdentifier { location; identifier } -> (
      (* As an LF term, plain identifiers are either term-level constants or
         variables (bound or free). *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Constant
          { location; identifier = qualified_identifier; operator }
      | QualifiedIdentifier.Dictionary.Entry Elaboration_state.LF_term ->
        (* Bound variable *)
        Synext'.CLF.Term.Variable { location; identifier }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        (* Free variable *)
        Synext'.CLF.Term.Variable { location; identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match elaborate_application state objects with
      | `Typ typ ->
        let location = Synext'.CLF.location_of_typ typ in
        raise @@ Expected_term location
      | `Term term -> term)
    | Synprs.CLF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (elaborate_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_term state body in
        Synext'.CLF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Elaboration_state.add_term name state in
        let body' = elaborate_term state' body in
        Synext'.CLF.Term.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawHole { location; variant } ->
      Synext'.CLF.Term.Hole { location; variant }
    | Synprs.CLF.Object.RawTuple { location; elements } ->
      let elements' = List1.map (elaborate_term state) elements in
      Synext'.CLF.Term.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.RawProjection { location; object_; projection } ->
      let term' = elaborate_term state object_ in
      Synext'.CLF.Term.Projection { location; term = term'; projection }
    | Synprs.CLF.Object.RawSubstitution { location; object_; substitution }
      ->
      let term' = elaborate_term state object_ in
      let substitution' = elaborate_substitution state substitution in
      Synext'.CLF.Term.Substitution
        { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.RawAnnotated { location; object_; sort } ->
      let term' = elaborate_term state object_
      and typ' = elaborate_typ state sort in
      Synext'.CLF.Term.TypeAnnotated { location; term = term'; typ = typ' }
    | Synprs.CLF.Object.RawParenthesized { location; object_ } ->
      let term' = elaborate_term state object_ in
      Synext'.CLF.Term.Parenthesized { location; term = term' }

  and elaborate_substitution state substitution =
    match substitution with
    | Synprs.CLF.Substitution.Empty { location } ->
      Synext'.CLF.Substitution.
        { location; extends_identity = false; terms = [] }
    | Synprs.CLF.Substitution.Identity { location } ->
      Synext'.CLF.Substitution.
        { location; extends_identity = true; terms = [] }
    | Synprs.CLF.Substitution.Substitution
        { location; extends_identity; objects } ->
      let terms' = List.map (elaborate_term state) (List1.to_list objects) in
      Synext'.CLF.Substitution.{ location; extends_identity; terms = terms' }

  (** [elaborate_arrows state arrow] elaborates the contextual LF arrow type
      [arrow]. Both forward and backward arrows were parsed as
      right-associative because the parser is top-down whereas bottom-up
      parsing is required to handle left and right-associative operators of
      the same precedence.

      This elaboration step uses Dijkstra's shunting yard algorithm in a
      simpler setting than that of {!elaborate_application}. *)
  and elaborate_arrows state =
    let module Arrow_operand = struct
      type t = Synext'.CLF.Typ.t
    end in
    let module Arrow_operator = struct
      type t =
        | Forward_arrow
        | Backward_arrow

      let arity _ = 2

      let precedence _ = 0

      let fixity _ = Fixity.infix

      let associativity = function
        | Forward_arrow -> Associativity.right_associative
        | Backward_arrow -> Associativity.left_associative

      include (
        Eq.Make (struct
          type nonrec t = t

          let equal = Stdlib.( = )
        end) :
          Eq.EQ with type t := t)
    end in
    let module Arrow_writer = struct
      (** [write operator operands] writes the application of the forward or
          backward infix arrow [operator] with the two operands [operands]. *)
      let write operator operands =
        let[@warning "-8"] [ left_operand; right_operand ] = operands in
        let location =
          Location.join
            (Synext'.CLF.location_of_typ left_operand)
            (Synext'.CLF.location_of_typ right_operand)
        in
        match operator with
        | Arrow_operator.Forward_arrow ->
          Synext'.CLF.Typ.ForwardArrow
            { location; domain = left_operand; range = right_operand }
        | Arrow_operator.Backward_arrow ->
          Synext'.CLF.Typ.BackwardArrow
            { location; range = left_operand; domain = right_operand }
    end in
    let module ShuntingYard =
      ShuntingYard.Make (Arrow_operand) (Arrow_operator) (Arrow_writer)
    in
    (* [flatten object_] reduces the chain of parsed right-associative arrows
       to an alternating list of operands (elaborated LF types) and operators
       (either forward or backward arrows). *)
    let rec flatten object_ =
      match object_ with
      | Synprs.CLF.Object.RawArrow
          { left_operand; right_operand; orientation = `Backward; _ } ->
        ShuntingYard.operand (elaborate_typ state left_operand)
        :: ShuntingYard.operator Arrow_operator.Backward_arrow
        :: flatten right_operand
      | Synprs.CLF.Object.RawArrow
          { left_operand; right_operand; orientation = `Forward; _ } ->
        ShuntingYard.operand (elaborate_typ state left_operand)
        :: ShuntingYard.operator Arrow_operator.Forward_arrow
        :: flatten right_operand
      | _ -> [ ShuntingYard.operand (elaborate_typ state object_) ]
    in
    fun arrow -> ShuntingYard.shunting_yard (flatten arrow)

  (** [elaborate_application state objects] elaborates [objects] as either a
      type-level or term-level contextual LF application with respect to the
      elaboration context [state].

      In both type-level and term-level contextual LF applications, arguments
      are contextual LF terms.

      This elaboration is in three steps:

      - First, LF type-level and term-level constants are identified as
        operators (with or without quoting) using [state], and the rest are
        identified as operands.
      - Second, consecutive operands are combined as an application
        (juxtaposition) that has yet to be elaborated, and written in prefix
        notation with the first operand being the application head.
      - Third, Dijkstra's shunting yard algorithm is used to rewrite the
        identified prefix, infix and postfix operators to applications. *)
  and elaborate_application state =
    let elaborate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term applicand | `Typ applicand ->
          Synprs.CLF.location_of_object applicand
      in
      let application_location =
        List.fold_left
          (fun acc operand ->
            Location.join acc (Synprs.CLF.location_of_object operand))
          applicand_location arguments
      in
      match applicand with
      | `Term applicand ->
        let applicand' = elaborate_term state applicand in
        let arguments' = List.map (elaborate_term state) arguments in
        `Term
          (Synext'.CLF.Term.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ applicand ->
        let applicand' = elaborate_typ state applicand in
        let arguments' = List.map (elaborate_term state) arguments in
        `Typ
          (Synext'.CLF.Typ.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module ShuntingYard =
      ShuntingYard.Make (CLF_operand) (CLF_operator)
        (struct
          (** [elaborate_argument argument] elaborates [argument] to an LF
              term.

              @raise Expected_term *)
          let elaborate_argument argument =
            match argument with
            | CLF_operand.External_term term -> term
            | CLF_operand.External_typ typ ->
              let location = Synext'.CLF.location_of_typ typ in
              raise @@ Expected_term location
            | CLF_operand.Parser_object object_ ->
              elaborate_term state object_
            | CLF_operand.Application { applicand; arguments } -> (
              match elaborate_juxtaposition applicand arguments with
              | `Term term -> term
              | `Typ typ ->
                let location = Synext'.CLF.location_of_typ typ in
                raise @@ Expected_term location)

          let elaborate_arguments arguments =
            List.map elaborate_argument arguments

          let write operator arguments =
            let application_location =
              List.fold_left
                (fun acc operand ->
                  Location.join acc (CLF_operand.location operand))
                (CLF_operator.location operator)
                arguments
            in
            match operator with
            | CLF_operator.Type_constant { applicand; _ } ->
              let applicand' = elaborate_typ state applicand in
              let arguments' = elaborate_arguments arguments in
              CLF_operand.External_typ
                (Synext'.CLF.Typ.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
            | CLF_operator.Term_constant { applicand; _ } ->
              let applicand' = elaborate_term state applicand in
              let arguments' = elaborate_arguments arguments in
              CLF_operand.External_term
                (Synext'.CLF.Term.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
        end)
    in
    (* [prepare_objects objects] identifies operators in [objects] and
       rewrites juxtapositions to applications in prefix notation. The
       objects themselves are not elaborated to LF types or terms yet. This
       is only done in the shunting yard algorithm so that the leftmost
       syntax error gets reported. *)
    let prepare_objects objects =
      (* Predicate for identified objects that may appear as juxtaposed
         arguments to an application in prefix notation. This predicate does
         not apply to the application head. *)
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (CLF_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_operand.Application
               { applicand = `Typ t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_operand.Application
               { applicand = `Term t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Typ t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_operand.Application
                 { applicand = `Term t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_operator.Term_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      objects |> List2.to_list
      |> List.map (fun term ->
             let tag = identify_lf_operator state term in
             (tag, term))
      |> reduce_juxtapositions_and_identify_operators
    in
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
        | CLF_operand.External_typ t -> `Typ t
        | CLF_operand.External_term t -> `Term t
        | CLF_operand.Application { applicand; arguments } ->
          elaborate_juxtaposition applicand arguments
        | CLF_operand.Parser_object _ ->
          Error.violation
            "[CLF.elaborate_application] unexpectedly did not elaborate LF \
             operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[CLF.elaborate_application] unexpectedly ended with an empty \
           expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[CLF.elaborate_application] unexpectedly ended with leftover \
           expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_operator.location operator
        and operand_locations = List.map CLF_operand.location operands in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier = CLF_operator.identifier left_operator
        and left_operator_location = CLF_operator.location left_operator
        and right_operator_location = CLF_operator.location right_operator in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_operator.identifier operator
        and operator_location = CLF_operator.location operator
        and actual_argument_locations =
          List.map CLF_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }

  (** Contextual LF term-level or type-level pattern operands for rewriting
      of prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_pattern_operand = struct
    (** The type of operands that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | External_typ_pattern of Synext'.CLF.Typ.Pattern.t
          (** An elaborated contextual LF type pattern. *)
      | External_term_pattern of Synext'.CLF.Term.Pattern.t
          (** An elaborated contextual LF term pattern. *)
      | Parser_object of Synprs.CLF.Object.t
          (** A contextual LF object that has yet to be elaborated. *)
      | Application of
          { applicand :
              [ `Typ_pattern of Synprs.CLF.Object.t
              | `Term_pattern of Synprs.CLF.Object.t
              ]
          ; arguments : Synprs.CLF.Object.t List.t
          }
          (** A contextual LF type-level or term-level application pattern. *)

    (** {1 Destructors} *)

    let location = function
      | External_typ_pattern t -> Synext'.CLF.location_of_typ_pattern t
      | External_term_pattern t -> Synext'.CLF.location_of_term_pattern t
      | Parser_object t -> Synprs.CLF.location_of_object t
      | Application { applicand; arguments } ->
        let applicand_location =
          match applicand with
          | `Typ_pattern applicand | `Term_pattern applicand ->
            Synprs.CLF.location_of_object applicand
        in
        List.fold_left
          (fun acc a -> Location.join acc (Synprs.CLF.location_of_object a))
          applicand_location arguments
  end

  (** Contextual LF term-level or type-level pattern operators for rewriting
      of prefix, infix and postfix operators using {!ShuntingYard}. *)
  module CLF_pattern_operator = struct
    (** The type of operators that may appear during rewriting of prefix,
        infix and postfix operators. *)
    type t =
      | Type_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF type-level constant with its operator
              definition in the elaboration context, and its corresponding
              AST. *)
      | Term_constant of
          { identifier : QualifiedIdentifier.t
          ; operator : Operator.t
          ; applicand : Synprs.CLF.Object.t
          }
          (** A contextual LF term-level constant with its operator
              definition in the elaboration context, and its corresponding
              AST. *)

    (** {1 Destructors} *)

    let[@inline] operator = function
      | Type_constant { operator; _ } | Term_constant { operator; _ } ->
        operator

    let[@inline] applicand = function
      | Type_constant { applicand; _ } | Term_constant { applicand; _ } ->
        applicand

    let[@inline] identifier = function
      | Type_constant { identifier; _ } | Term_constant { identifier; _ } ->
        identifier

    let arity = Fun.(operator >> Operator.arity)

    let precedence = Fun.(operator >> Operator.precedence)

    let fixity = Fun.(operator >> Operator.fixity)

    let associativity = Fun.(operator >> Operator.associativity)

    let location = Fun.(applicand >> Synprs.CLF.location_of_object)

    (** {1 Instances} *)

    (** Equality instance on type-level and term-level constants. Since
        operator identifiers share the same namespace, operators having the
        same name are equal in a rewriting of an application. *)
    include (
      (val Eq.contramap (module QualifiedIdentifier) identifier) :
        Eq.EQ with type t := t)
  end

  (** [elaborate_typ state object_] is [object_] rewritten as a contextual LF
      type pattern with respect to the elaboration context [state].

      Type pattern applications are rewritten with
      {!elaborate_application_pattern} using Dijkstra's shunting yard
      algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF types, see the Beluga language specification.

      Examples of invalid type patterns that may result from this elaboration
      include:

      - [c x x], where [x] is a free pattern variable *)
  let rec elaborate_typ_pattern state object_ =
    match object_ with
    | Synprs.CLF.Object.RawLambda { location; _ } ->
      raise @@ Illegal_lambda_type_pattern location
    | Synprs.CLF.Object.RawAnnotated { location; _ } ->
      raise @@ Illegal_annotated_type_pattern location
    | Synprs.CLF.Object.RawPi { location; parameter_sort = Option.None; _ }
      -> raise @@ Illegal_pi_type_pattern location
    | Synprs.CLF.Object.RawTuple { location; _ } ->
      raise @@ Illegal_tuple_type_pattern location
    | Synprs.CLF.Object.RawProjection { location; _ } ->
      raise @@ Illegal_projection_type_pattern location
    | Synprs.CLF.Object.RawSubstitution { location; _ } ->
      raise @@ Illegal_substitution_type_pattern location
    | Synprs.CLF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_type_pattern location
    | Synprs.CLF.Object.RawHole
        { location; variant = `Unlabelled | `Labelled _ } ->
      raise @@ Illegal_labellable_hole_type_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_type_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_type_pattern location
    | Synprs.CLF.Object.RawHole { location; variant = `Underscore } ->
      Synext'.CLF.Typ.Pattern.Wildcard { location }
    | Synprs.CLF.Object.RawIdentifier { location; identifier } -> (
      (* As an LF type pattern, plain identifiers are either type-level
         constants, variables already present in the pattern, or new pattern
         variables. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Pattern.Constant
          { location; identifier = qualified_identifier; operator }
      | _ -> Synext'.CLF.Typ.Pattern.Variable { location; identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF type pattern, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily type-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_type_constant operator) ->
        Synext'.CLF.Typ.Pattern.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_type_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_type_constant { location; identifier })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match elaborate_application_pattern state objects with
      | `Term_pattern term_pattern ->
        let location = Synext'.CLF.location_of_term_pattern term_pattern in
        raise @@ Expected_type_pattern location
      | `Typ_pattern typ_pattern -> typ_pattern)
    | Synprs.CLF.Object.RawBlock { location; elements = x, xs } ->
      let elements' =
        ( Pair.map_right (elaborate_typ_pattern state) x
        , List.map (Pair.map_right (elaborate_typ_pattern state)) xs )
      in
      Synext'.CLF.Typ.Pattern.Block { location; elements = elements' }
    | Synprs.CLF.Object.RawParenthesized { location; object_ } ->
      let pattern' = elaborate_typ_pattern state object_ in
      Synext'.CLF.Typ.Pattern.Parenthesized { location; pattern = pattern' }

  (** [elaborate_term_pattern state object_] is [object_] rewritten as a
      contextual LF term pattern with respect to the elaboration context
      [state].

      Term applications are rewritten with {!elaborate_application_pattern}
      using Dijkstra's shunting yard algorithm.

      This function imposes syntactic restrictions on [object_], but does not
      perform normalization nor validation. To see the syntactic restrictions
      from LF objects to LF terms, see the Beluga language specification.

      Examples of invalid term patterns that may result from this elaboration
      include:

      - [c x x], where [x] is a free pattern variable *)
  and elaborate_term_pattern state object_ =
    match object_ with
    | Synprs.CLF.Object.RawPi { location; _ } ->
      raise @@ Illegal_pi_term_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Forward; _ } ->
      raise @@ Illegal_forward_arrow_term_pattern location
    | Synprs.CLF.Object.RawArrow { location; orientation = `Backward; _ } ->
      raise @@ Illegal_backward_arrow_term_pattern location
    | Synprs.CLF.Object.RawBlock { location; _ } ->
      raise @@ Illegal_block_term_pattern location
    | Synprs.CLF.Object.RawHole
        { location; variant = `Unlabelled | `Labelled _ } ->
      raise @@ Illegal_labellable_hole_term_pattern location
    | Synprs.CLF.Object.RawIdentifier { location; identifier } -> (
      (* As an LF term pattern, plain identifiers are either term-level
         constants, variables already present in the pattern, or new pattern
         variables. *)
      let qualified_identifier =
        QualifiedIdentifier.make_simple identifier
      in
      match Elaboration_state.lookup qualified_identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Pattern.Constant
          { location; identifier = qualified_identifier; operator }
      | _ -> Synext'.CLF.Term.Pattern.Variable { location; identifier })
    | Synprs.CLF.Object.RawQualifiedIdentifier { location; identifier } -> (
      (* Qualified identifiers without modules were parsed as plain
         identifiers *)
      assert (List.length (QualifiedIdentifier.modules identifier) >= 1);
      (* As an LF term pattern, identifiers of the form [(<identifier> `::')+
         <identifier>] are necessarily term-level constants. *)
      match Elaboration_state.lookup identifier state with
      | QualifiedIdentifier.Dictionary.Entry
          (Elaboration_state.LF_term_constant operator) ->
        Synext'.CLF.Term.Pattern.Constant { location; identifier; operator }
      | entry ->
        raise @@ Expected_term_constant { location; actual_binding = entry }
      | exception QualifiedIdentifier.Dictionary.Unbound_identifier _ ->
        raise @@ Unbound_term_constant { location; identifier })
    | Synprs.CLF.Object.RawApplication { objects; _ } -> (
      match elaborate_application_pattern state objects with
      | `Typ_pattern typ_pattern ->
        let location = Synext'.CLF.location_of_typ_pattern typ_pattern in
        raise @@ Expected_term_pattern location
      | `Term_pattern term_pattern -> term_pattern)
    | Synprs.CLF.Object.RawLambda
        { location; parameter_identifier; parameter_sort; body } -> (
      let parameter_type' =
        Option.map (elaborate_typ state) parameter_sort
      in
      match parameter_identifier with
      | Option.None ->
        let body' = elaborate_term_pattern state body in
        Synext'.CLF.Term.Pattern.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          }
      | Option.Some name ->
        let state' = Elaboration_state.add_term name state in
        let body' = elaborate_term_pattern state' body in
        Synext'.CLF.Term.Pattern.Abstraction
          { location
          ; parameter_identifier
          ; parameter_type = parameter_type'
          ; body = body'
          })
    | Synprs.CLF.Object.RawHole { location; variant = `Underscore } ->
      Synext'.CLF.Term.Pattern.Wildcard { location }
    | Synprs.CLF.Object.RawTuple { location; elements } ->
      let elements' = List1.map (elaborate_term_pattern state) elements in
      Synext'.CLF.Term.Pattern.Tuple { location; terms = elements' }
    | Synprs.CLF.Object.RawProjection { location; object_; projection } ->
      let term' = elaborate_term_pattern state object_ in
      Synext'.CLF.Term.Pattern.Projection
        { location; term = term'; projection }
    | Synprs.CLF.Object.RawSubstitution { location; object_; substitution }
      ->
      let term' = elaborate_term_pattern state object_ in
      let substitution' = elaborate_substitution state substitution in
      Synext'.CLF.Term.Pattern.Substitution
        { location; term = term'; substitution = substitution' }
    | Synprs.CLF.Object.RawAnnotated { location; object_; sort } ->
      let term' = elaborate_term_pattern state object_
      and typ' = elaborate_typ state sort in
      Synext'.CLF.Term.Pattern.TypeAnnotated
        { location; term = term'; typ = typ' }
    | Synprs.CLF.Object.RawParenthesized { location; object_ } ->
      let pattern' = elaborate_term_pattern state object_ in
      Synext'.CLF.Term.Pattern.Parenthesized { location; pattern = pattern' }

  (** [elaborate_application_pattern state objects] elaborates [objects] as
      either a type-level or term-level LF application with respect to the
      elaboration context [state].

      In both type-level and term-level LF applications, arguments are LF
      terms.

      This elaboration is in three steps:

      - First, LF type-level and term-level constants are identified as
        operators (with or without quoting) using [state], and the rest are
        identified as operands.
      - Second, consecutive operands are combined as an application
        (juxtaposition) that has yet to be elaborated, and written in prefix
        notation with the first operand being the application head.
      - Third, Dijkstra's shunting yard algorithm is used to rewrite the
        identified prefix, infix and postfix operators to applications. *)
  and elaborate_application_pattern state =
    let elaborate_juxtaposition applicand arguments =
      let applicand_location =
        match applicand with
        | `Term_pattern applicand | `Typ_pattern applicand ->
          Synprs.CLF.location_of_object applicand
      in
      let application_location =
        List.fold_left
          (fun acc operand ->
            Location.join acc (Synprs.CLF.location_of_object operand))
          applicand_location arguments
      in
      match applicand with
      | `Term_pattern applicand ->
        let applicand' = elaborate_term_pattern state applicand in
        let arguments' = List.map (elaborate_term_pattern state) arguments in
        `Term_pattern
          (Synext'.CLF.Term.Pattern.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
      | `Typ_pattern applicand ->
        let applicand' = elaborate_typ_pattern state applicand in
        let arguments' = List.map (elaborate_term_pattern state) arguments in
        `Typ_pattern
          (Synext'.CLF.Typ.Pattern.Application
             { location = application_location
             ; applicand = applicand'
             ; arguments = arguments'
             })
    in
    let module ShuntingYard =
      ShuntingYard.Make (CLF_pattern_operand) (CLF_pattern_operator)
        (struct
          (** [elaborate_argument argument] elaborates [argument] to an LF
              term.

              @raise Expected_term_pattern *)
          let elaborate_argument argument =
            match argument with
            | CLF_pattern_operand.External_term_pattern term -> term
            | CLF_pattern_operand.External_typ_pattern typ_pattern ->
              let location =
                Synext'.CLF.location_of_typ_pattern typ_pattern
              in
              raise @@ Expected_term_pattern location
            | CLF_pattern_operand.Parser_object object_ ->
              elaborate_term_pattern state object_
            | CLF_pattern_operand.Application { applicand; arguments } -> (
              match elaborate_juxtaposition applicand arguments with
              | `Term_pattern term_pattern -> term_pattern
              | `Typ_pattern typ_pattern ->
                let location =
                  Synext'.CLF.location_of_typ_pattern typ_pattern
                in
                raise @@ Expected_term_pattern location)

          let elaborate_arguments arguments =
            List.map elaborate_argument arguments

          let write operator arguments =
            let application_location =
              List.fold_left
                (fun acc operand ->
                  Location.join acc (CLF_pattern_operand.location operand))
                (CLF_pattern_operator.location operator)
                arguments
            in
            match operator with
            | CLF_pattern_operator.Type_constant { applicand; _ } ->
              let applicand' = elaborate_typ_pattern state applicand in
              let arguments' = elaborate_arguments arguments in
              CLF_pattern_operand.External_typ_pattern
                (Synext'.CLF.Typ.Pattern.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
            | CLF_pattern_operator.Term_constant { applicand; _ } ->
              let applicand' = elaborate_term_pattern state applicand in
              let arguments' = elaborate_arguments arguments in
              CLF_pattern_operand.External_term_pattern
                (Synext'.CLF.Term.Pattern.Application
                   { location = application_location
                   ; applicand = applicand'
                   ; arguments = arguments'
                   })
        end)
    in
    (* [prepare_objects objects] identifies operators in [objects] and
       rewrites juxtapositions to applications in prefix notation. The
       objects themselves are not elaborated to LF types or terms yet. This
       is only done in the shunting yard algorithm so that the leftmost
       syntax error gets reported. *)
    let prepare_objects objects =
      (* Predicate for identified objects that may appear as juxtaposed
         arguments to an application in prefix notation. This predicate does
         not apply to the application head. *)
      let is_argument = function
        | `Not_an_operator, _
        | `Quoted_type_operator, _
        | `Quoted_term_operator, _ -> true
        | `Type_operator (_, operator), _ | `Term_operator (_, operator), _
          -> Operator.is_nullary operator
      in
      let rec reduce_juxtapositions_and_identify_operators objects =
        match objects with
        | (`Not_an_operator, t) :: ts -> (
          match List.take_while is_argument ts with
          | [], rest (* [t] is an operand not in juxtaposition *) ->
            ShuntingYard.operand (CLF_pattern_operand.Parser_object t)
            :: reduce_juxtapositions_and_identify_operators rest
          | arguments, rest
          (* [t] is an applicand in juxtaposition with [arguments] *) ->
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Term_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest)
        | (`Quoted_type_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_pattern_operand.Application
               { applicand = `Typ_pattern t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Quoted_term_operator, t) :: ts ->
          let arguments, rest = List.take_while is_argument ts in
          let arguments' = List.map Pair.snd arguments in
          ShuntingYard.operand
            (CLF_pattern_operand.Application
               { applicand = `Term_pattern t; arguments = arguments' })
          :: reduce_juxtapositions_and_identify_operators rest
        | (`Type_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Typ_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_pattern_operator.Type_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | (`Term_operator (identifier, operator), t) :: ts ->
          if Operator.is_prefix operator then
            let arguments, rest = List.take_while is_argument ts in
            let arguments' = List.map Pair.snd arguments in
            ShuntingYard.operand
              (CLF_pattern_operand.Application
                 { applicand = `Term_pattern t; arguments = arguments' })
            :: reduce_juxtapositions_and_identify_operators rest
          else
            ShuntingYard.operator
              (CLF_pattern_operator.Term_constant
                 { identifier; operator; applicand = t })
            :: reduce_juxtapositions_and_identify_operators ts
        | [] -> []
      in
      objects |> List2.to_list
      |> List.map (fun term ->
             let tag = identify_lf_operator state term in
             (tag, term))
      |> reduce_juxtapositions_and_identify_operators
    in
    fun objects ->
      try
        match ShuntingYard.shunting_yard (prepare_objects objects) with
        | CLF_pattern_operand.External_typ_pattern t -> `Typ_pattern t
        | CLF_pattern_operand.External_term_pattern t -> `Term_pattern t
        | CLF_pattern_operand.Application { applicand; arguments } ->
          elaborate_juxtaposition applicand arguments
        | CLF_pattern_operand.Parser_object _ ->
          Error.violation
            "[CLF.elaborate_application_pattern] unexpectedly did not \
             elaborate LF operands in rewriting"
      with
      | ShuntingYard.Empty_expression ->
        Error.violation
          "[CLF.elaborate_application_pattern] unexpectedly ended with an \
           empty expression"
      | ShuntingYard.Leftover_expressions _ ->
        Error.violation
          "[CLF.elaborate_application_pattern] unexpectedly ended with \
           leftover expressions"
      | ShuntingYard.Misplaced_operator { operator; operands } ->
        let operator_location = CLF_pattern_operator.location operator
        and operand_locations =
          List.map CLF_pattern_operand.location operands
        in
        raise @@ Misplaced_operator { operator_location; operand_locations }
      | ShuntingYard.Consecutive_non_associative_operators
          { left_operator; right_operator } ->
        let operator_identifier =
          CLF_pattern_operator.identifier left_operator
        and left_operator_location =
          CLF_pattern_operator.location left_operator
        and right_operator_location =
          CLF_pattern_operator.location right_operator
        in
        raise
        @@ Consecutive_non_associative_operators
             { operator_identifier
             ; left_operator_location
             ; right_operator_location
             }
      | ShuntingYard.Arity_mismatch { operator; operator_arity; operands } ->
        let operator_identifier = CLF_pattern_operator.identifier operator
        and operator_location = CLF_pattern_operator.location operator
        and actual_argument_locations =
          List.map CLF_pattern_operand.location operands
        in
        raise
        @@ Arity_mismatch
             { operator_identifier
             ; operator_location
             ; operator_arity
             ; actual_argument_locations
             }
end
