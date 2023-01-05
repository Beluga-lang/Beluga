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
  include State.STATE

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

  val empty : state

  (** {2 Binding additions} *)

  val add_lf_term_variable : Identifier.t -> Unit.t t

  val add_prefix_lf_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> Unit.t t

  val add_infix_lf_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> Unit.t t

  val add_postfix_lf_type_constant :
    precedence:Int.t -> Identifier.t -> Unit.t t

  val add_prefix_lf_term_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> Unit.t t

  val add_infix_lf_term_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> Unit.t t

  val add_postfix_lf_term_constant :
    precedence:Int.t -> Identifier.t -> Unit.t t

  val add_meta_variable : Identifier.t -> Unit.t t

  val add_parameter_variable : Identifier.t -> Unit.t t

  val add_substitution_variable : Identifier.t -> Unit.t t

  val add_context_variable : Identifier.t -> Unit.t t

  val add_schema_constant : Identifier.t -> Unit.t t

  val add_computation_variable : Identifier.t -> Unit.t t

  val add_prefix_computation_type_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> Unit.t t

  val add_infix_computation_type_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> Unit.t t

  val add_postfix_computation_type_constant :
    precedence:Int.t -> Identifier.t -> Unit.t t

  val add_prefix_computation_term_constructor :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> Unit.t t

  val add_infix_computation_term_constructor :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> Unit.t t

  val add_postfix_computation_term_constructor :
    precedence:Int.t -> Identifier.t -> Unit.t t

  val add_prefix_computation_cotype_constant :
    arity:Int.t -> precedence:Int.t -> Identifier.t -> Unit.t t

  val add_infix_computation_cotype_constant :
       associativity:Associativity.t
    -> precedence:Int.t
    -> Identifier.t
    -> Unit.t t

  val add_postfix_computation_cotype_constant :
    precedence:Int.t -> Identifier.t -> Unit.t t

  val add_computation_term_destructor : Identifier.t -> Unit.t t

  val add_query : Identifier.t -> Unit.t t

  val add_mquery : Identifier.t -> Unit.t t

  val add_module :
    entry List1.t Identifier.Hamt.t -> Identifier.t -> Unit.t t

  (** {2 Getters, setters and mutators} *)

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t

  val get_bindings : entry List1.t Identifier.Hamt.t t

  val modify_bindings :
       (entry List1.t Identifier.Hamt.t -> entry List1.t Identifier.Hamt.t)
    -> Unit.t t

  val modify_binding :
       modify_entry:(entry -> entry)
    -> modify_module:
         (entry List1.t Identifier.Hamt.t -> entry List1.t Identifier.Hamt.t)
    -> Qualified_identifier.t
    -> Unit.t t

  val pop_binding : Identifier.t -> Unit.t t

  exception Expected_operator of Qualified_identifier.t

  val modify_operator :
    (Operator.t -> Operator.t) -> Qualified_identifier.t -> Unit.t t

  (** {1 Lookups} *)

  exception Unbound_identifier of Identifier.t

  exception Unbound_qualified_identifier of Qualified_identifier.t

  exception Expected_toplevel_namespace of Identifier.t

  exception Unbound_namespace of Qualified_identifier.t

  exception Expected_namespace of Qualified_identifier.t

  val lookup : Qualified_identifier.t -> (entry, exn) Result.t t

  val lookup_toplevel : Identifier.t -> (entry, exn) Result.t t

  (** {1 Checkpoints} *)

  val mark_bindings : Unit.t t

  exception No_bindings_checkpoint

  val rollback_bindings : Unit.t t

  (** {1 Tracking} *)

  val track_variable : (Identifier.t -> Unit.t t) -> Identifier.t -> Unit.t t

  val clear_tracked_variables : Unit.t t

  val get_tracked_variables : Identifier.t List.t t
end

(** A minimal disambiguation state backed by nested HAMT datastructures with
    plain identifier keys. *)
module Disambiguation_state : DISAMBIGUATION_STATE = struct
  type entry =
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

  type state =
    { bindings : entry List1.t Identifier.Hamt.t List1.t
          (** Symbol table with checkpoints. *)
    ; default_associativity : Associativity.t
          (** Associativity to use if a pragma for an infix operator does not
              specify an associativity. *)
    ; tracked_variables : Identifier.t List.t
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let empty =
    { bindings = List1.singleton Identifier.Hamt.empty
    ; default_associativity = Associativity.non_associative
    ; tracked_variables = []
    }

  let[@inline] set_default_associativity default_associativity =
    let* state = get in
    put { state with default_associativity }

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let get_bindings =
    let* state = get in
    return (List1.head state.bindings)

  let get_checkpoints =
    let* state = get in
    return (List1.tail state.bindings)

  let[@inline] set_bindings bindings =
    let* checkpoints = get_checkpoints in
    let* state = get in
    put { state with bindings = List1.from bindings checkpoints }

  let mark_bindings =
    let* bindings = get_bindings in
    let* state = get in
    put { state with bindings = List1.cons bindings state.bindings }

  exception No_bindings_checkpoint

  let rollback_bindings =
    get_checkpoints >>= function
    | latest_checkpoint :: later_checkpoints ->
        let* state = get in
        put
          { state with
            bindings = List1.from latest_checkpoint later_checkpoints
          }
    | [] -> Error.raise No_bindings_checkpoint

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

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
    | Option.Some entry -> Result.ok (List1.head entry)
    | Option.None -> Result.error (Unbound_identifier query)

  let lookup_namespace query bindings =
    match lookup_entry query bindings with
    | Result.Ok (Module { entries }) -> Result.ok entries
    | Result.Ok (LF_type_constant _)
    | Result.Ok (LF_term_constant _)
    | Result.Ok LF_term_variable
    | Result.Ok Meta_variable
    | Result.Ok Parameter_variable
    | Result.Ok Substitution_variable
    | Result.Ok Context_variable
    | Result.Ok Schema_constant
    | Result.Ok Computation_variable
    | Result.Ok (Computation_type_constant _)
    | Result.Ok (Computation_term_constructor _)
    | Result.Ok (Computation_cotype_constant _)
    | Result.Ok Computation_term_destructor
    | Result.Ok Query
    | Result.Ok MQuery ->
        Result.error (Expected_toplevel_namespace query)
    | Result.Error _ as e -> e

  let lookup query =
    let* bindings = get_bindings in
    let namespaces = Qualified_identifier.modules query in
    match namespaces with
    | [] ->
        let name = Qualified_identifier.name query in
        return (lookup_entry name bindings)
    | namespaces -> (
        let bindings', _looked_up_namespaces =
          List.fold_left
            (fun (bindings, looked_up_namespaces) namespace ->
              match lookup_namespace namespace bindings with
              | Result.Ok bindings' ->
                  (bindings', namespace :: looked_up_namespaces)
              | Result.Error (Unbound_identifier _) ->
                  let namespace_qualified_identifier =
                    Qualified_identifier.make
                      ~modules:(List.rev looked_up_namespaces)
                      namespace
                  in
                  Error.raise
                    (Unbound_namespace namespace_qualified_identifier)
              | Result.Error (Expected_toplevel_namespace _) ->
                  let namespace_qualified_identifier =
                    Qualified_identifier.make
                      ~modules:(List.rev looked_up_namespaces)
                      namespace
                  in
                  Error.raise
                    (Expected_namespace namespace_qualified_identifier)
              | Result.Error cause -> Error.raise cause)
            (bindings, []) namespaces
        in
        let name = Qualified_identifier.name query in
        match lookup_entry name bindings' with
        | Result.Ok entry -> return (Result.ok entry)
        | Result.Error (Unbound_identifier _identifier) ->
            return (Result.error (Unbound_qualified_identifier query))
        | Result.Error cause -> Error.raise cause)

  let lookup_toplevel query =
    let* bindings = get_bindings in
    return (lookup_entry query bindings)

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

  let modify_binding ~modify_entry ~modify_module identifier =
    lookup identifier >>= function
    | Result.Ok (Module { entries }) ->
        let entries' = modify_module entries in
        let entry' = Module { entries = entries' } in
        modify_bindings (add_nested identifier entry')
    | Result.Ok entry ->
        let entry' = modify_entry entry in
        modify_bindings (add_nested identifier entry')
    | Result.Error cause -> raise cause

  exception Expected_operator of Qualified_identifier.t

  let modify_operator f identifier =
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
      identifier

  let clear_tracked_variables =
    let* state = get in
    put { state with tracked_variables = [] }

  let get_tracked_variables =
    let* state = get in
    return state.tracked_variables

  let track_variable add identifier =
    let* () = add identifier in
    let* state = get in
    put
      { state with
        tracked_variables = identifier :: state.tracked_variables
      }

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
