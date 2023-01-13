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

exception Expected_namespace of Qualified_identifier.t

exception Expected_operator of Qualified_identifier.t

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Unbound_namespace of Qualified_identifier.t

exception Bound_lf_type_constant of Qualified_identifier.t

exception Bound_lf_term_constant of Qualified_identifier.t

exception Bound_lf_term_variable of Qualified_identifier.t

exception Bound_meta_variable of Qualified_identifier.t

exception Bound_parameter_variable of Qualified_identifier.t

exception Bound_substitution_variable of Qualified_identifier.t

exception Bound_context_variable of Qualified_identifier.t

exception Bound_schema_constant of Qualified_identifier.t

exception Bound_computation_variable of Qualified_identifier.t

exception Bound_computation_inductive_type_constant of Qualified_identifier.t

exception
  Bound_computation_stratified_type_constant of Qualified_identifier.t

exception
  Bound_computation_coinductive_type_constant of Qualified_identifier.t

exception
  Bound_computation_abbreviation_type_constant of Qualified_identifier.t

exception Bound_computation_term_constructor of Qualified_identifier.t

exception Bound_computation_term_destructor of Qualified_identifier.t

exception Bound_query of Qualified_identifier.t

exception Bound_mquery of Qualified_identifier.t

exception Bound_module of Qualified_identifier.t

module type BINDINGS_STATE = sig
  include State.STATE

  type entry = private
    | Lf_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Lf_term_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Lf_term_variable of { location : Location.t }
    | Meta_variable of { location : Location.t }
    | Parameter_variable of { location : Location.t }
    | Substitution_variable of { location : Location.t }
    | Context_variable of { location : Location.t }
    | Schema_constant of { location : Location.t }
    | Computation_variable of { location : Location.t }
    | Computation_inductive_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_stratified_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_coinductive_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_abbreviation_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_term_constructor of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_term_destructor of { location : Location.t }
    | Query of { location : Location.t }
    | MQuery of { location : Location.t }
    | Module of
        { location : Location.t
        ; state : state
        }

  val empty : state

  val add_lf_term_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_lf_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_meta_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_context_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_schema_constant : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_computation_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_inductive_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_stratified_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_coinductive_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_abbreviation_computation_type_constant :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_computation_term_constructor :
    ?location:Location.t -> Operator.t -> Identifier.t -> Unit.t t

  val add_computation_term_destructor :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_query : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_mquery : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_module : ?location:Location.t -> state -> Identifier.t -> Unit.t t

  val actual_binding_exn : Qualified_identifier.t -> entry -> exn

  val pop_binding : Identifier.t -> Unit.t t

  val open_namespace : Qualified_identifier.t -> (Unit.t, exn) Result.t t

  val modify_operator :
    (Operator.t -> Operator.t) -> Qualified_identifier.t -> Unit.t t

  val lookup : Qualified_identifier.t -> (entry, exn) Result.t t

  val lookup_toplevel : Identifier.t -> (entry, exn) Result.t t

  val partial_lookup :
       Qualified_identifier.t
    -> [ `Partially_bound of
         (Identifier.t * entry) List1.t * Identifier.t List1.t
       | `Totally_bound of (Identifier.t * entry) List1.t
       | `Totally_unbound of Identifier.t List1.t
       ]
       t
end

module type TRAILING_BINDINGS_STATE = sig
  include State.STATE

  val mark_bindings : Unit.t t

  val rollback_bindings : Unit.t t
end

module type SIGNATURE_STATE = sig
  include State.STATE

  val set_default_associativity : Associativity.t -> Unit.t t

  val get_default_associativity : Associativity.t t
end

(** Module type for the type of state used in disambiguating the parser
    syntax to the external syntax. *)
module type DISAMBIGUATION_STATE = sig
  include State.STATE

  include BINDINGS_STATE with type state := state

  include TRAILING_BINDINGS_STATE with type state := state

  include SIGNATURE_STATE with type state := state

  (** [with_lf_term_variable identifier a] runs [a] in a state where there is
      a bound LF term variable [identifier]. After having run [a], the added
      variable [identifier] is removed. *)
  val with_lf_term_variable : Identifier.t -> 'a t -> 'a t

  val with_lf_term_variable_opt : Identifier.t Option.t -> 'a t -> 'a t

  val with_pattern_variables_checkpoint :
    pattern:'a t -> expression:'b t -> ('a * 'b) t
end

(** A minimal disambiguation state backed by nested HAMT data structures with
    plain identifier keys. *)
module Disambiguation_state : DISAMBIGUATION_STATE = struct
  type entry =
    | Lf_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Lf_term_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Lf_term_variable of { location : Location.t }
    | Meta_variable of { location : Location.t }
    | Parameter_variable of { location : Location.t }
    | Substitution_variable of { location : Location.t }
    | Context_variable of { location : Location.t }
    | Schema_constant of { location : Location.t }
    | Computation_variable of { location : Location.t }
    | Computation_inductive_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_stratified_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_coinductive_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_abbreviation_type_constant of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_term_constructor of
        { location : Location.t
        ; operator : Operator.t
        }
    | Computation_term_destructor of { location : Location.t }
    | Query of { location : Location.t }
    | MQuery of { location : Location.t }
    | Module of
        { location : Location.t
        ; state : state
        }

  and state =
    { bindings : entry List1.t Identifier.Hamt.t List1.t
          (** Symbol table with checkpoints. *)
    ; default_associativity : Associativity.t
          (** Associativity to use if a pragma for an infix operator does not
              specify an associativity. *)
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let empty =
    { bindings = List1.singleton Identifier.Hamt.empty
    ; default_associativity = Associativity.non_associative
    }

  let[@inline] set_default_associativity default_associativity =
    modify (fun state -> { state with default_associativity })

  let get_default_associativity =
    let* state = get in
    return state.default_associativity

  let get_checkpoints =
    let* state = get in
    return (List1.tail state.bindings)

  let get_bindings =
    let* state = get in
    return (List1.head state.bindings)

  let[@inline] set_bindings bindings =
    let* checkpoints = get_checkpoints in
    modify (fun state ->
        { state with bindings = List1.from bindings checkpoints })

  let mark_bindings =
    let* bindings = get_bindings in
    modify (fun state ->
        { state with bindings = List1.cons bindings state.bindings })

  let rollback_bindings =
    get_checkpoints >>= function
    | latest_checkpoint :: later_checkpoints ->
        modify (fun state ->
            { state with
              bindings = List1.from latest_checkpoint later_checkpoints
            })
    | [] ->
        Error.violation "[rollback_bindings] no checkpoint to rollback to"

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let[@inline] push_binding identifier entry bindings =
    match Identifier.Hamt.find_opt identifier bindings with
    | Option.None ->
        Identifier.Hamt.add identifier (List1.singleton entry) bindings
    | Option.Some binding_stack ->
        Identifier.Hamt.add identifier
          (List1.cons entry binding_stack)
          bindings

  let[@inline] add_binding identifier entry =
    modify_bindings (push_binding identifier entry)

  let make_entry_location location identifier =
    Option.value location ~default:(Identifier.location identifier)

  let add_lf_term_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Lf_term_variable { location } in
    add_binding identifier entry

  let add_lf_type_constant ?location operator identifier =
    let location = make_entry_location location identifier in
    let entry = Lf_type_constant { location; operator } in
    add_binding identifier entry

  let add_lf_term_constant ?location operator identifier =
    let location = make_entry_location location identifier in
    let entry = Lf_term_constant { location; operator } in
    add_binding identifier entry

  let add_meta_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Meta_variable { location } in
    add_binding identifier entry

  let add_parameter_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Parameter_variable { location } in
    add_binding identifier entry

  let add_substitution_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Substitution_variable { location } in
    add_binding identifier entry

  let add_context_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Context_variable { location } in
    add_binding identifier entry

  let add_schema_constant ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Schema_constant { location } in
    add_binding identifier entry

  let add_computation_variable ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Computation_variable { location } in
    add_binding identifier entry

  let add_inductive_computation_type_constant ?location operator identifier =
    let location = make_entry_location location identifier in
    let entry = Computation_inductive_type_constant { location; operator } in
    add_binding identifier entry

  let add_stratified_computation_type_constant ?location operator identifier
      =
    let location = make_entry_location location identifier in
    let entry =
      Computation_stratified_type_constant { location; operator }
    in
    add_binding identifier entry

  let add_coinductive_computation_type_constant ?location operator identifier
      =
    let location = make_entry_location location identifier in
    let entry =
      Computation_coinductive_type_constant { location; operator }
    in
    add_binding identifier entry

  let add_abbreviation_computation_type_constant ?location operator
      identifier =
    let location = make_entry_location location identifier in
    let entry =
      Computation_abbreviation_type_constant { location; operator }
    in
    add_binding identifier entry

  let add_computation_term_constructor ?location operator identifier =
    let location = make_entry_location location identifier in
    let entry = Computation_term_constructor { location; operator } in
    add_binding identifier entry

  let add_computation_term_destructor ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Computation_term_destructor { location } in
    add_binding identifier entry

  let add_query ?location identifier =
    let location = make_entry_location location identifier in
    let entry = Query { location } in
    add_binding identifier entry

  let add_mquery ?location identifier =
    let location = make_entry_location location identifier in
    let entry = MQuery { location } in
    add_binding identifier entry

  let add_module ?location state identifier =
    let location = make_entry_location location identifier in
    let entry = Module { location; state } in
    add_binding identifier entry

  let lookup_toplevel query =
    let* bindings = get_bindings in
    match Identifier.Hamt.find_opt query bindings with
    | Option.Some binding_stack ->
        return (Result.ok (List1.head binding_stack))
    | Option.None -> return (Result.error (Unbound_identifier query))

  let modify_toplevel_namespace modify identifier =
    lookup_toplevel identifier >>= function
    | Result.Ok (Lf_type_constant _)
    | Result.Ok (Lf_term_constant _)
    | Result.Ok (Lf_term_variable _)
    | Result.Ok (Meta_variable _)
    | Result.Ok (Parameter_variable _)
    | Result.Ok (Substitution_variable _)
    | Result.Ok (Context_variable _)
    | Result.Ok (Schema_constant _)
    | Result.Ok (Computation_variable _)
    | Result.Ok (Computation_inductive_type_constant _)
    | Result.Ok (Computation_stratified_type_constant _)
    | Result.Ok (Computation_coinductive_type_constant _)
    | Result.Ok (Computation_abbreviation_type_constant _)
    | Result.Ok (Computation_term_constructor _)
    | Result.Ok (Computation_term_destructor _)
    | Result.Ok (Query _)
    | Result.Ok (MQuery _) ->
        Error.raise
          (Unbound_namespace (Qualified_identifier.make_simple identifier))
    | Result.Ok (Module { location; state } as entry) ->
        let state', a = run (modify entry) state in
        let* () = add_module ~location state' identifier in
        return a
    | Result.Error cause -> Error.raise cause

  let try_catch_lookup namespace =
    try_catch ~on_exn:(function
      | Unbound_namespace namespace' ->
          let namespace'' =
            Qualified_identifier.prepend_module namespace namespace'
          in
          Error.raise (Unbound_namespace namespace'')
      | Unbound_identifier identifier ->
          let identifier' =
            Qualified_identifier.prepend_module namespace
              (Qualified_identifier.make_simple identifier)
          in
          Error.raise (Unbound_qualified_identifier identifier')
      | Unbound_qualified_identifier identifier ->
          let identifier' =
            Qualified_identifier.prepend_module namespace identifier
          in
          Error.raise (Unbound_qualified_identifier identifier')
      | cause -> Error.raise cause)

  let rec set_nested ~namespaces ~identifier entry =
    match namespaces with
    | [] -> modify_bindings (push_binding identifier entry)
    | namespace :: namespaces' ->
        modify_toplevel_namespace
          (fun _ ->
            try_catch_lookup namespace
              (set_nested ~namespaces:namespaces' ~identifier entry))
          namespace

  let set qualified_identifier entry =
    let identifier = Qualified_identifier.name qualified_identifier
    and namespaces = Qualified_identifier.modules qualified_identifier in
    set_nested ~namespaces ~identifier entry

  let rec lookup_nested ~namespaces ~identifier =
    match namespaces with
    | [] -> lookup_toplevel identifier
    | namespace :: namespaces' ->
        modify_toplevel_namespace
          (fun _ ->
            try_catch_lookup namespace
              (lookup_nested ~namespaces:namespaces' ~identifier))
          namespace

  let lookup query entry =
    let identifier = Qualified_identifier.name query
    and namespaces = Qualified_identifier.modules query in
    lookup_nested ~namespaces ~identifier entry

  let rec partial_lookup_nested = function
    | List1.T (identifier, []) -> (
        lookup_toplevel identifier >>= function
        | Result.Ok entry ->
            return (`Totally_bound (List1.singleton (identifier, entry)))
        | Result.Error (Unbound_identifier _) ->
            return (`Totally_unbound (List1.singleton identifier))
        | Result.Error cause -> Error.raise cause)
    | List1.T (x1, x2 :: xs) as identifiers ->
        try_catch
          (modify_toplevel_namespace
             (fun namespace_entry ->
               partial_lookup_nested (List1.from x2 xs) >>= function
               | `Totally_bound xs' ->
                   return
                     (`Totally_bound (List1.cons (x1, namespace_entry) xs'))
               | `Partially_bound (bound, unbound) ->
                   return
                     (`Partially_bound
                       (List1.cons (x1, namespace_entry) bound, unbound))
               | `Totally_unbound xs' ->
                   return
                     (`Partially_bound
                       (List1.singleton (x1, namespace_entry), xs')))
             x1)
          ~on_exn:(function
            | Unbound_namespace _ -> (
                lookup_toplevel x1 >>= function
                | Result.Ok entry ->
                    return
                      (`Partially_bound
                        (List1.singleton (x1, entry), List1.from x2 xs))
                | Result.Error cause -> Error.raise cause)
            | Unbound_identifier _ -> return (`Totally_unbound identifiers)
            | cause -> Error.raise cause)

  let partial_lookup query =
    let identifier = Qualified_identifier.name query
    and namespaces = Qualified_identifier.modules query in
    partial_lookup_nested
      (List1.append_list namespaces (List1.singleton identifier))

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

  let modify_operator f identifier =
    lookup identifier >>= function
    | Result.Ok (Lf_type_constant entry) ->
        set identifier
          (Lf_type_constant { entry with operator = f entry.operator })
    | Result.Ok (Lf_term_constant entry) ->
        set identifier
          (Lf_term_constant { entry with operator = f entry.operator })
    | Result.Ok (Computation_inductive_type_constant entry) ->
        set identifier
          (Computation_inductive_type_constant
             { entry with operator = f entry.operator })
    | Result.Ok (Computation_stratified_type_constant entry) ->
        set identifier
          (Computation_stratified_type_constant
             { entry with operator = f entry.operator })
    | Result.Ok (Computation_abbreviation_type_constant entry) ->
        set identifier
          (Computation_abbreviation_type_constant
             { entry with operator = f entry.operator })
    | Result.Ok (Computation_coinductive_type_constant entry) ->
        set identifier
          (Computation_coinductive_type_constant
             { entry with operator = f entry.operator })
    | Result.Ok (Computation_term_constructor entry) ->
        set identifier
          (Computation_term_constructor
             { entry with operator = f entry.operator })
    | Result.Ok (Lf_term_variable _)
    | Result.Ok (Meta_variable _)
    | Result.Ok (Parameter_variable _)
    | Result.Ok (Substitution_variable _)
    | Result.Ok (Context_variable _)
    | Result.Ok (Schema_constant _)
    | Result.Ok (Computation_variable _)
    | Result.Ok (Computation_term_destructor _)
    | Result.Ok (Query _)
    | Result.Ok (MQuery _)
    | Result.Ok (Module _) ->
        Error.raise (Expected_operator identifier)
    | Result.Error cause -> Error.raise cause

  let actual_binding_exn identifier = function
    | Lf_type_constant { location; _ } ->
        Error.located_exception1 location (Bound_lf_type_constant identifier)
    | Lf_term_constant { location; _ } ->
        Error.located_exception1 location (Bound_lf_term_constant identifier)
    | Lf_term_variable { location } ->
        Error.located_exception1 location (Bound_lf_term_variable identifier)
    | Meta_variable { location } ->
        Error.located_exception1 location (Bound_meta_variable identifier)
    | Parameter_variable { location } ->
        Error.located_exception1 location
          (Bound_parameter_variable identifier)
    | Substitution_variable { location } ->
        Error.located_exception1 location
          (Bound_substitution_variable identifier)
    | Context_variable { location } ->
        Error.located_exception1 location (Bound_context_variable identifier)
    | Schema_constant { location } ->
        Error.located_exception1 location (Bound_schema_constant identifier)
    | Computation_variable { location } ->
        Error.located_exception1 location
          (Bound_computation_variable identifier)
    | Computation_inductive_type_constant { location; _ } ->
        Error.located_exception1 location
          (Bound_computation_inductive_type_constant identifier)
    | Computation_stratified_type_constant { location; _ } ->
        Error.located_exception1 location
          (Bound_computation_stratified_type_constant identifier)
    | Computation_coinductive_type_constant { location; _ } ->
        Error.located_exception1 location
          (Bound_computation_coinductive_type_constant identifier)
    | Computation_abbreviation_type_constant { location; _ } ->
        Error.located_exception1 location
          (Bound_computation_abbreviation_type_constant identifier)
    | Computation_term_constructor { location; _ } ->
        Error.located_exception1 location
          (Bound_computation_term_constructor identifier)
    | Computation_term_destructor { location } ->
        Error.located_exception1 location
          (Bound_computation_term_destructor identifier)
    | Query { location } ->
        Error.located_exception1 location (Bound_query identifier)
    | MQuery { location } ->
        Error.located_exception1 location (Bound_mquery identifier)
    | Module { location; _ } ->
        Error.located_exception1 location (Bound_module identifier)

  let open_namespace identifier =
    lookup identifier >>= function
    | Result.Ok (Lf_type_constant _)
    | Result.Ok (Lf_term_constant _)
    | Result.Ok (Lf_term_variable _)
    | Result.Ok (Meta_variable _)
    | Result.Ok (Parameter_variable _)
    | Result.Ok (Substitution_variable _)
    | Result.Ok (Context_variable _)
    | Result.Ok (Schema_constant _)
    | Result.Ok (Computation_variable _)
    | Result.Ok (Computation_inductive_type_constant _)
    | Result.Ok (Computation_stratified_type_constant _)
    | Result.Ok (Computation_coinductive_type_constant _)
    | Result.Ok (Computation_abbreviation_type_constant _)
    | Result.Ok (Computation_term_constructor _)
    | Result.Ok (Computation_term_destructor _)
    | Result.Ok (Query _)
    | Result.Ok (MQuery _) ->
        return (Result.error (Expected_namespace identifier))
    | Result.Ok (Module { state; location }) ->
        let state', bindings' = get_bindings state in
        let* () = set identifier (Module { state = state'; location }) in
        let* () =
          modify_bindings (fun bindings ->
              Identifier.Hamt.union
                (fun _key _original_binding new_binding -> new_binding)
                bindings bindings')
        in
        return (Result.ok ())
    | Result.Error cause -> return (Result.error cause)

  let with_lf_term_variable identifier =
    scoped
      ~set:(add_lf_term_variable identifier)
      ~unset:(pop_binding identifier)

  let with_lf_term_variable_opt identifier_opt =
    match identifier_opt with
    | Option.None -> Fun.id
    | Option.Some identifier -> with_lf_term_variable identifier

  let with_pattern_variables_checkpoint = Obj.magic ()
end

let pp_exception ppf = function
  | Expected_operator qualified_identifier ->
      Format.fprintf ppf "Expected an operator bound at %a."
        Qualified_identifier.pp qualified_identifier
  | Unbound_identifier identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Identifier.pp identifier
  | Unbound_qualified_identifier qualified_identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Qualified_identifier.pp
        qualified_identifier
  | Unbound_namespace qualified_identifier ->
      Format.fprintf ppf "Unbound namespace %a." Qualified_identifier.pp
        qualified_identifier
  | Expected_namespace qualified_identifier ->
      Format.fprintf ppf "Expected a namespace %a." Qualified_identifier.pp
        qualified_identifier
  | Bound_lf_type_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_lf_term_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF term constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_lf_term_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound LF term variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_meta_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound meta-variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_parameter_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound parameter variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_substitution_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound substitution variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_context_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound context variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_schema_constant qualified_identifier ->
      Format.fprintf ppf "%a is a bound schema constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_variable qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation variable."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_inductive_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level inductive type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_stratified_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level stratified type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_coinductive_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level coinductive type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_abbreviation_type_constant qualified_identifier ->
      Format.fprintf ppf
        "%a is a bound computation-level abbreviation type constant."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_term_constructor qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation-level term constructor."
        Qualified_identifier.pp qualified_identifier
  | Bound_computation_term_destructor qualified_identifier ->
      Format.fprintf ppf "%a is a bound computation-level term destructor."
        Qualified_identifier.pp qualified_identifier
  | Bound_query qualified_identifier ->
      Format.fprintf ppf "%a is a bound query." Qualified_identifier.pp
        qualified_identifier
  | Bound_mquery qualified_identifier ->
      Format.fprintf ppf "%a is a bound mquery." Qualified_identifier.pp
        qualified_identifier
  | Bound_module qualified_identifier ->
      Format.fprintf ppf "%a is a bound module." Qualified_identifier.pp
        qualified_identifier
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
