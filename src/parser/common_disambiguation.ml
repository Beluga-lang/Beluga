(** Disambiguation of the parser syntax to the external syntax.

    Elements of the syntax for Beluga require the symbol table for
    disambiguation. This module contains stateful functions for elaborating
    the context-free parser syntax to the data-dependent external syntax. The
    logic for the symbol lookups is repeated in the indexing phase to the
    approximate syntax.

    The "Beluga Language Specification" document contains additional details
    as to which syntactic structures have ambiguities. *)

open Support
open Beluga_syntax

(** Module type for the type of state used in disambiguating the parser
    syntax to the external syntax. *)
module type DISAMBIGUATION_STATE = sig
  type t

  type entry = private
    | LF_type_constant of { operator : Operator.t }
    | LF_term_constant of { operator : Operator.t }
    | LF_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_type_constant of { operator : Operator.t }
    | Computation_term_constructor of { operator : Operator.t }
    | Computation_cotype_constant of { operator : Operator.t }
    | Computation_term_destructor
    | Query
    | MQuery
    | Module of { entries : entry List1.t Identifier.Hamt.t }

  (** {1 Constructors} *)

  val empty : t

  (** {2 Binding additions} *)

  val add_lf_term_variable : Identifier.t -> t -> t

  val add_prefix_lf_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_lf_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_lf_type_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_lf_term_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_lf_term_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_meta_variable : Identifier.t -> t -> t

  val add_parameter_variable : Identifier.t -> t -> t

  val add_substitution_variable : Identifier.t -> t -> t

  val add_context_variable : Identifier.t -> t -> t

  val add_schema_constant : Identifier.t -> t -> t

  val add_computation_variable : Identifier.t -> t -> t

  val add_prefix_computation_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_type_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_computation_term_constructor :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_term_constructor :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_term_constructor :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_prefix_computation_cotype_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> t -> t

  val add_infix_computation_cotype_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> t
    -> t

  val add_postfix_computation_cotype_constant :
    precedence:Int.t -> Identifier.t -> t -> t

  val add_computation_term_destructor : Identifier.t -> t -> t

  val add_query : Identifier.t -> t -> t

  val add_mquery : Identifier.t -> t -> t

  val add_module : entry List1.t Identifier.Hamt.t -> Identifier.t -> t -> t

  (** {2 Getters, setters and mutators} *)

  val set_default_associativity : Associativity.t -> t -> t

  val get_default_associativity : t -> Associativity.t

  val get_bindings : t -> entry List1.t Identifier.Hamt.t

  val modify_bindings :
       (entry List1.t Identifier.Hamt.t -> entry List1.t Identifier.Hamt.t)
    -> t
    -> t

  val modify_binding :
       modify_entry:(entry -> entry)
    -> modify_module:
         (entry List1.t Identifier.Hamt.t -> entry List1.t Identifier.Hamt.t)
    -> Qualified_identifier.t
    -> t
    -> t

  val pop_binding : Identifier.t -> t -> t

  exception Expected_operator of Qualified_identifier.t

  val modify_operator :
    (Operator.t -> Operator.t) -> Qualified_identifier.t -> t -> t

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Expected_toplevel_namespace of Identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  exception Expected_namespace of Qualified_identifier.t

  val lookup : Qualified_identifier.t -> t -> entry

  val lookup_toplevel : Identifier.t -> t -> entry
end

(** A minimal disambiguation state backed by nested HAMT datastructures with
    plain identifier keys. *)
module Disambiguation_state : DISAMBIGUATION_STATE = struct
  type t =
    { bindings : entry List1.t Identifier.Hamt.t  (** Symbol table. *)
    ; default_associativity : Associativity.t
          (** Associativity to use if a pragma for an infix operator does not
              specify an associativity. *)
    }

  and entry =
    | LF_type_constant of { operator : Operator.t }
    | LF_term_constant of { operator : Operator.t }
    | LF_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_type_constant of { operator : Operator.t }
    | Computation_term_constructor of { operator : Operator.t }
    | Computation_cotype_constant of { operator : Operator.t }
    | Computation_term_destructor
    | Query
    | MQuery
    | Module of { entries : entry List1.t Identifier.Hamt.t }

  let empty =
    { bindings = Identifier.Hamt.empty
    ; default_associativity = Associativity.non_associative
    }

  let[@inline] set_default_associativity default_associativity state =
    { state with default_associativity }

  let[@inline] get_default_associativity state = state.default_associativity

  let[@inline] set_bindings bindings state = { state with bindings }

  let[@inline] get_bindings state = state.bindings

  let[@inline] modify_bindings f state =
    let bindings' = f state.bindings in
    set_bindings bindings' state

  let[@inline] push_binding identifier entry bindings =
    match Identifier.Hamt.find_opt identifier bindings with
    | Option.None ->
        Identifier.Hamt.add identifier (List1.singleton entry) bindings
    | Option.Some stack ->
        Identifier.Hamt.add identifier (List1.cons entry stack) bindings

  let[@inline] add_binding identifier entry =
    modify_bindings (push_binding identifier entry)

  let add_lf_term_variable identifier =
    let entry = LF_term_variable in
    add_binding identifier entry

  let add_prefix_lf_type_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    let entry = LF_type_constant { operator } in
    add_binding identifier entry

  let add_infix_lf_type_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    let entry = LF_type_constant { operator } in
    add_binding identifier entry

  let add_postfix_lf_type_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    let entry = LF_type_constant { operator } in
    add_binding identifier entry

  let add_prefix_lf_term_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    let entry = LF_term_constant { operator } in
    add_binding identifier entry

  let add_infix_lf_term_constant ~associativity ~precedence identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    let entry = LF_term_constant { operator } in
    add_binding identifier entry

  let add_postfix_lf_term_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    let entry = LF_term_constant { operator } in
    add_binding identifier entry

  let add_meta_variable identifier =
    let entry = Meta_variable in
    add_binding identifier entry

  let add_parameter_variable identifier =
    let entry = Parameter_variable in
    add_binding identifier entry

  let add_substitution_variable identifier =
    let entry = Substitution_variable in
    add_binding identifier entry

  let add_context_variable identifier =
    let entry = Context_variable in
    add_binding identifier entry

  let add_schema_constant identifier =
    let entry = Schema_constant in
    add_binding identifier entry

  let add_computation_variable identifier =
    let entry = Computation_variable in
    add_binding identifier entry

  let add_prefix_computation_type_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    let entry = Computation_type_constant { operator } in
    add_binding identifier entry

  let add_infix_computation_type_constant ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    let entry = Computation_type_constant { operator } in
    add_binding identifier entry

  let add_postfix_computation_type_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    let entry = Computation_type_constant { operator } in
    add_binding identifier entry

  let add_prefix_computation_term_constructor ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    let entry = Computation_term_constructor { operator } in
    add_binding identifier entry

  let add_infix_computation_term_constructor ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    let entry = Computation_term_constructor { operator } in
    add_binding identifier entry

  let add_postfix_computation_term_constructor ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    let entry = Computation_term_constructor { operator } in
    add_binding identifier entry

  let add_prefix_computation_cotype_constant ~arity ~precedence identifier =
    let operator = Operator.make_prefix ~arity ~precedence in
    let entry = Computation_cotype_constant { operator } in
    add_binding identifier entry

  let add_infix_computation_cotype_constant ~associativity ~precedence
      identifier =
    let operator = Operator.make_infix ~associativity ~precedence in
    let entry = Computation_cotype_constant { operator } in
    add_binding identifier entry

  let add_postfix_computation_cotype_constant ~precedence identifier =
    let operator = Operator.make_postfix ~precedence in
    let entry = Computation_cotype_constant { operator } in
    add_binding identifier entry

  let add_computation_term_destructor identifier =
    let entry = Computation_term_destructor in
    add_binding identifier entry

  let add_query identifier =
    let entry = Query in
    add_binding identifier entry

  let add_mquery identifier =
    let entry = MQuery in
    add_binding identifier entry

  let add_module entries identifier =
    let entry = Module { entries } in
    add_binding identifier entry

  let add_nested qualified_identifier entry bindings =
    let identifier = Qualified_identifier.name qualified_identifier
    and modules = Qualified_identifier.modules qualified_identifier in
    match modules with
    | [] (* Toplevel declaration *) -> push_binding identifier entry bindings
    | m :: ms (* Nested declaration *) ->
        let rec add_lookup module_to_lookup next_modules bindings =
          let stack' =
            match Identifier.Hamt.find_opt module_to_lookup bindings with
            | Option.Some (List1.T (Module { entries }, stack))
            (* Addition to existing module *) ->
                let entries' =
                  match next_modules with
                  | [] (* Finished lookups *) ->
                      push_binding identifier entry entries
                  | m :: ms (* Recursively lookup next module *) ->
                      add_lookup m ms entries
                in
                List1.from (Module { entries = entries' }) stack
            | Option.Some stack (* Entry shadowing *) ->
                let entries =
                  match next_modules with
                  | [] (* Finished lookups *) ->
                      push_binding identifier entry Identifier.Hamt.empty
                  | m :: ms (* Recursively lookup next module *) ->
                      add_lookup m ms Identifier.Hamt.empty
                in
                List1.cons (Module { entries }) stack
            | Option.None (* Module introduction *) ->
                let entries =
                  match next_modules with
                  | [] (* Finished lookups *) ->
                      push_binding identifier entry Identifier.Hamt.empty
                  | m :: ms (* Recursively lookup next module *) ->
                      add_lookup m ms Identifier.Hamt.empty
                in
                List1.singleton (Module { entries })
          in
          Identifier.Hamt.add module_to_lookup stack' bindings
        in
        add_lookup m ms bindings

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Expected_toplevel_namespace of Identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  exception Expected_namespace of Qualified_identifier.t

  let lookup_entry query bindings =
    match Identifier.Hamt.find_opt query bindings with
    | Option.Some entry -> List1.head entry
    | Option.None -> raise (Unbound_identifier query)

  let lookup_namespace query bindings =
    match lookup_entry query bindings with
    | Module { entries } -> entries
    | LF_type_constant _
    | LF_term_constant _
    | LF_term_variable
    | Meta_variable
    | Parameter_variable
    | Substitution_variable
    | Context_variable
    | Schema_constant
    | Computation_variable
    | Computation_type_constant _
    | Computation_term_constructor _
    | Computation_cotype_constant _
    | Computation_term_destructor
    | Query
    | MQuery ->
        raise (Expected_toplevel_namespace query)

  let lookup query state =
    let bindings = get_bindings state in
    let namespaces = Qualified_identifier.modules query in
    match namespaces with
    | [] ->
        let name = Qualified_identifier.name query in
        lookup_entry name bindings
    | namespaces -> (
        let bindings', _looked_up_namespaces =
          List.fold_left
            (fun (bindings, looked_up_namespaces) namespace ->
              try
                let bindings' = lookup_namespace namespace bindings in
                (bindings', namespace :: looked_up_namespaces)
              with
              | Unbound_identifier _ ->
                  let namespace_qualified_identifier =
                    Qualified_identifier.make
                      ~modules:(List.rev looked_up_namespaces)
                      namespace
                  in
                  raise (Unbound_namespace namespace_qualified_identifier)
              | Expected_toplevel_namespace _ ->
                  let namespace_qualified_identifier =
                    Qualified_identifier.make
                      ~modules:(List.rev looked_up_namespaces)
                      namespace
                  in
                  raise (Expected_namespace namespace_qualified_identifier))
            (bindings, []) namespaces
        in
        let name = Qualified_identifier.name query in
        try lookup_entry name bindings' with
        | Unbound_identifier _identifier ->
            raise (Unbound_qualified_identifier query))

  let lookup_toplevel query state =
    let bindings = get_bindings state in
    lookup_entry query bindings

  let[@inline] pop_binding identifier =
    modify_bindings (fun bindings ->
        match Identifier.Hamt.find_opt identifier bindings with
        | Option.None -> raise (Unbound_identifier identifier)
        | Option.Some (List1.T (_head_to_discard, new_head :: stack)) ->
            Identifier.Hamt.add identifier
              (List1.from new_head stack)
              bindings
        | Option.Some (List1.T (_head_to_discard, [])) ->
            Identifier.Hamt.remove identifier bindings)

  let modify_binding ~modify_entry ~modify_module identifier state =
    match lookup identifier state with
    | Module { entries } ->
        let entries' = modify_module entries in
        let entry' = Module { entries = entries' } in
        (modify_bindings (add_nested identifier entry')) state
    | entry ->
        let entry' = modify_entry entry in
        (modify_bindings (add_nested identifier entry')) state

  exception Expected_operator of Qualified_identifier.t

  let modify_operator f identifier state =
    modify_binding
      ~modify_entry:(function
        | LF_type_constant { operator } ->
            let operator' = f operator in
            LF_type_constant { operator = operator' }
        | LF_term_constant { operator } ->
            let operator' = f operator in
            LF_term_constant { operator = operator' }
        | Computation_type_constant { operator } ->
            let operator' = f operator in
            Computation_type_constant { operator = operator' }
        | Computation_term_constructor { operator } ->
            let operator' = f operator in
            Computation_term_constructor { operator = operator' }
        | Computation_cotype_constant { operator } ->
            let operator' = f operator in
            Computation_cotype_constant { operator = operator' }
        | LF_term_variable
        | Meta_variable
        | Parameter_variable
        | Substitution_variable
        | Context_variable
        | Schema_constant
        | Computation_variable
        | Computation_term_destructor
        | Query
        | MQuery
        | Module _ ->
            raise (Expected_operator identifier))
      ~modify_module:(fun _entry -> raise (Expected_operator identifier))
      identifier state

  let pp_exception ppf = function
    | Expected_operator qualified_identifier ->
        Format.fprintf ppf "Expected an operator bound at %a"
          Qualified_identifier.pp qualified_identifier
    | Unbound_identifier identifier ->
        Format.fprintf ppf "Identifier %a is unbound" Identifier.pp
          identifier
    | Unbound_qualified_identifier qualified_identifier ->
        Format.fprintf ppf "Identifier %a is unbound" Qualified_identifier.pp
          qualified_identifier
    | Expected_toplevel_namespace identifier ->
        Format.fprintf ppf "Expected a toplevel namespace %a" Identifier.pp
          identifier
    | Unbound_namespace qualified_identifier ->
        Format.fprintf ppf "Unbound namespace %a" Qualified_identifier.pp
          qualified_identifier
    | Expected_namespace qualified_identifier ->
        Format.fprintf ppf "Expected a namespace %a" Qualified_identifier.pp
          qualified_identifier
    | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some (Format.stringify pp_exception exn) with
        | Invalid_argument _ -> Option.none)
end
