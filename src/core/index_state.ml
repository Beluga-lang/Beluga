open Support
open Beluga_syntax

[@@@warning "-A-4-44"] (* TODO: *)

exception Bound_lf_type_constant of Qualified_identifier.t

exception Bound_lf_term_constant of Qualified_identifier.t

exception Bound_lf_term_variable of Qualified_identifier.t

exception Bound_meta_variable of Qualified_identifier.t

exception Bound_parameter_variable of Qualified_identifier.t

exception Bound_substitution_variable of Qualified_identifier.t

exception Bound_context_variable of Qualified_identifier.t

exception Bound_contextual_variable of Qualified_identifier.t

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

exception Bound_module of Qualified_identifier.t

exception Bound_program_constant of Qualified_identifier.t

exception Expected_lf_typ_constant

exception Expected_lf_term_constant

exception Expected_schema_constant

exception Expected_computation_inductive_type_constant

exception Expected_computation_stratified_type_constant

exception Expected_computation_coinductive_type_constant

exception Expected_computation_abbreviation_type_constant

exception Expected_computation_term_constructor

exception Expected_computation_term_destructor

exception Expected_program_constant

exception Expected_lf_term_variable

exception Expected_meta_variable

exception Expected_parameter_variable

exception Expected_substitution_variable

exception Expected_context_variable

exception Expected_computation_variable

exception Illegal_free_variable

module type INDEXING_STATE = sig
  include State.STATE

  val fresh_identifier : Identifier.t t

  val fresh_identifier_opt : Identifier.t Option.t -> Identifier.t t

  val index_of_lf_typ_constant : Qualified_identifier.t -> Id.cid_typ t

  val index_of_lf_term_constant : Qualified_identifier.t -> Id.cid_term t

  val index_of_inductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_stratified_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typ t

  val index_of_coinductive_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_cotyp t

  val index_of_abbreviation_comp_constant :
    Qualified_identifier.t -> Id.cid_comp_typdef t

  val index_of_schema_constant : Qualified_identifier.t -> Id.cid_schema t

  val index_of_comp_constructor :
    Qualified_identifier.t -> Id.cid_comp_const t

  val index_of_comp_destructor : Qualified_identifier.t -> Id.cid_comp_dest t

  val index_of_comp_program : Qualified_identifier.t -> Id.cid_prog t

  val index_of_lf_variable : Identifier.t -> Id.offset t

  val index_of_lf_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_meta_variable : Identifier.t -> Id.offset t

  val index_of_meta_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_parameter_variable : Identifier.t -> Id.offset t

  val index_of_parameter_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_substitution_variable : Identifier.t -> Id.offset t

  val index_of_substitution_variable_opt :
    Identifier.t -> Id.offset Option.t t

  val index_of_context_variable : Identifier.t -> Id.offset t

  val index_of_context_variable_opt : Identifier.t -> Id.offset Option.t t

  val index_of_comp_variable : Identifier.t -> Id.offset t

  val with_bound_lf_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_meta_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_parameter_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_substitution_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_context_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_contextual_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_bound_comp_variable :
    ?location:Location.t -> Identifier.t -> 'a t -> 'a t

  val with_shifted_lf_context : 'a t -> 'a t

  val with_shifted_meta_context : 'a t -> 'a t

  val with_shifted_comp_context : 'a t -> 'a t

  val add_lf_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t t

  val add_lf_term_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t t

  val add_schema_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t t

  val add_inductive_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_stratified_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typ -> Unit.t t

  val add_coinductive_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_cotyp -> Unit.t t

  val add_abbreviation_computation_type_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_typdef -> Unit.t t

  val add_computation_term_constructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_const -> Unit.t t

  val add_computation_term_destructor :
    ?location:Location.t -> Identifier.t -> Id.cid_comp_dest -> Unit.t t

  val add_program_constant :
    ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t t

  val start_module : Unit.t t

  val stop_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> Unit.t t

  val add_module :
    ?location:Location.t -> Identifier.t -> Id.module_id -> 'a t -> 'a t

  val with_scope : 'a t -> 'a t

  val with_parent_scope : 'a t -> 'a t

  val with_free_variables_as_pattern_variables :
    pattern:'a t -> expression:('a -> 'b t) -> 'b t

  val add_computation_pattern_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_lf_variable : ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_meta_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_parameter_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_substitution_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val add_free_context_variable :
    ?location:Location.t -> Identifier.t -> Unit.t t

  val allow_free_variables : 'a t -> 'a t

  val disallow_free_variables : 'a t -> 'a t
end

module type LEVEL = sig
  type t

  val of_int : Int.t -> t

  val to_int : t -> Int.t
end

module Level = struct
  type t = int

  let of_int = Fun.id

  let to_int = Fun.id
end

module Lf_level : LEVEL = Level

module Meta_level : LEVEL = Level

module Comp_level : LEVEL = Level

module Persistent_indexing_state = struct
  type entry =
    { binding_location : Location.t
    ; desc : entry_desc
    }

  and entry_desc =
    | Lf_variable of { lf_level : Lf_level.t }
    | Meta_variable of { meta_level : Meta_level.t }
    | Parameter_variable of { meta_level : Meta_level.t }
    | Substitution_variable of { meta_level : Meta_level.t }
    | Context_variable of { meta_level : Meta_level.t }
    | Contextual_variable of { meta_level : Meta_level.t }
        (** A contextual variable is either a meta, parameter, substitution,
            or contextual variable. Contextual variables are introduced
            ambiguously by [mlam]-expressions. *)
    | Computation_variable of { comp_level : Comp_level.t }
    | Lf_type_constant of { cid : Id.cid_typ }
    | Lf_term_constant of { cid : Id.cid_term }
    | Schema_constant of { cid : Id.cid_schema }
    | Computation_inductive_type_constant of { cid : Id.cid_comp_typ }
    | Computation_stratified_type_constant of { cid : Id.cid_comp_typ }
    | Computation_coinductive_type_constant of { cid : Id.cid_comp_cotyp }
    | Computation_abbreviation_type_constant of { cid : Id.cid_comp_typdef }
    | Computation_term_constructor of { cid : Id.cid_comp_const }
    | Computation_term_destructor of { cid : Id.cid_comp_dest }
    | Program_constant of { cid : Id.cid_prog }
    | Module of { cid : Id.module_id }

  type bindings_state =
    { bindings : entry Binding_tree.t
    ; lf_context_size : Int.t
          (** The length of [cPsi], the context of LF-bound variables. *)
    ; meta_context_size : Int.t
          (** The length of [cD], the context of meta-level variables. *)
    ; comp_context_size : Int.t
          (** The length of [cG], the context of computation-level variables. *)
    }

  type substate =
    | Scope_state of
        { bindings : bindings_state
        ; parent : substate Option.t
        }
    | Pattern_state of
        { pattern_bindings : bindings_state
        ; inner_pattern_bindings : entry List1.t Identifier.Hamt.t
        ; pattern_variables_rev : Identifier.t List.t
        ; expression_bindings : bindings_state
        }

  type state =
    { substate : substate
    ; free_variables_allowed : Bool.t
    ; generated_fresh_variables_count : Int.t
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let get_and_increment_generated_fresh_variables_count =
    let* state = get in
    let i = state.generated_fresh_variables_count in
    let* () =
      put
        { state with
          generated_fresh_variables_count =
            state.generated_fresh_variables_count + 1
        }
    in
    return i

  let fresh_identifier =
    let* i = get_and_increment_generated_fresh_variables_count in
    (* ['"'] is a reserved character, so ["\"i1"], ["\"i2"], ..., etc. are
       syntactically invalid identifiers, which are guarenteed to not clash
       with free variables *)
    return (Identifier.make ("\"i" ^ string_of_int i))

  let fresh_identifier_opt = function
    | Option.Some identifier -> return identifier
    | Option.None -> fresh_identifier

  let[@inline] set_substate substate =
    modify (fun state -> { state with substate })

  let get_substate =
    let* state = get in
    return state.substate

  let[@inline] modify_substate f =
    let* substate = get_substate in
    let substate' = f substate in
    set_substate substate'

  let[@inline] set_substate_bindings bindings = function
    | Scope_state state -> Scope_state { state with bindings }
    | Pattern_state state ->
        Pattern_state { state with pattern_bindings = bindings }

  let get_substate_bindings = function
    | Scope_state state -> state.bindings
    | Pattern_state state -> state.pattern_bindings

  let[@inline] set_bindings_state bindings =
    modify_substate (set_substate_bindings bindings)

  let get_bindings_state = get_substate $> get_substate_bindings

  let[@inline] modify_bindings_state f =
    let* bindings_state = get_bindings_state in
    let bindings_state' = f bindings_state in
    set_bindings_state bindings_state'

  let set_bindings bindings =
    modify_bindings_state (fun state -> { state with bindings })

  let get_bindings =
    let* bindings_state = get_bindings_state in
    return bindings_state.bindings

  let[@inline] modify_bindings f =
    let* bindings = get_bindings in
    let bindings' = f bindings in
    set_bindings bindings'

  let get_lf_context_size =
    let* bindings_state = get_bindings_state in
    return bindings_state.lf_context_size

  let[@inline] set_lf_context_size lf_context_size =
    modify_bindings_state (fun state -> { state with lf_context_size })

  let[@inline] modify_lf_context_size f =
    let* lf_context_size = get_lf_context_size in
    let lf_context_size' = f lf_context_size in
    set_lf_context_size lf_context_size'

  let get_meta_context_size =
    let* bindings_state = get_bindings_state in
    return bindings_state.meta_context_size

  let[@inline] set_meta_context_size meta_context_size =
    modify_bindings_state (fun state -> { state with meta_context_size })

  let[@inline] modify_meta_context_size f =
    let* meta_context_size = get_meta_context_size in
    let meta_context_size' = f meta_context_size in
    set_meta_context_size meta_context_size'

  let get_comp_context_size =
    let* bindings_state = get_bindings_state in
    return bindings_state.comp_context_size

  let[@inline] set_comp_context_size comp_context_size =
    modify_bindings_state (fun state -> { state with comp_context_size })

  let[@inline] modify_comp_context_size f =
    let* comp_context_size = get_comp_context_size in
    let comp_context_size' = f comp_context_size in
    set_comp_context_size comp_context_size'

  let[@inline] lookup qualified_identifier =
    let* bindings = get_bindings in
    let entry, _subtree =
      Binding_tree.lookup qualified_identifier bindings
    in
    return entry

  let[@inline] lookup_toplevel identifier =
    let* bindings = get_bindings in
    let entry, _subtree = Binding_tree.lookup_toplevel identifier bindings in
    return entry

  let actual_binding_exn identifier { binding_location; desc } =
    Error.located_exception1 binding_location
      (match desc with
      | Lf_variable _ -> Bound_lf_term_variable identifier
      | Meta_variable _ -> Bound_meta_variable identifier
      | Parameter_variable _ -> Bound_parameter_variable identifier
      | Substitution_variable _ -> Bound_substitution_variable identifier
      | Context_variable _ -> Bound_context_variable identifier
      | Contextual_variable _ -> Bound_contextual_variable identifier
      | Computation_variable _ -> Bound_computation_variable identifier
      | Lf_type_constant _ -> Bound_lf_type_constant identifier
      | Lf_term_constant _ -> Bound_lf_term_constant identifier
      | Schema_constant _ -> Bound_schema_constant identifier
      | Computation_inductive_type_constant _ ->
          Bound_computation_inductive_type_constant identifier
      | Computation_stratified_type_constant _ ->
          Bound_computation_stratified_type_constant identifier
      | Computation_coinductive_type_constant _ ->
          Bound_computation_coinductive_type_constant identifier
      | Computation_abbreviation_type_constant _ ->
          Bound_computation_abbreviation_type_constant identifier
      | Computation_term_constructor _ ->
          Bound_computation_term_constructor identifier
      | Computation_term_destructor _ ->
          Bound_computation_term_destructor identifier
      | Program_constant _ -> Bound_program_constant identifier
      | Module _ -> Bound_module identifier)

  let index_of_lf_typ_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Lf_type_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_lf_typ_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_lf_term_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Lf_term_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_lf_term_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_inductive_comp_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_inductive_type_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_inductive_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_stratified_comp_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_stratified_type_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_stratified_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_coinductive_comp_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_coinductive_type_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_coinductive_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_abbreviation_comp_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_abbreviation_type_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_abbreviation_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_schema_constant qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Schema_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_schema_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_constructor qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_term_constructor { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_computation_term_constructor
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_destructor qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Computation_term_destructor { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_computation_term_destructor
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_program qualified_identifier =
    lookup qualified_identifier $> function
    | { desc = Program_constant { cid }; _ } -> cid
    | entry ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_program_constant
             (actual_binding_exn qualified_identifier entry))

  let[@inline] index_of_variable_opt index_of_variable identifier =
    try_catch
      (lazy (index_of_variable identifier $> Option.some))
      ~on_exn:(function
        | Binding_tree.Unbound_identifier _ -> return Option.none
        | cause -> Error.raise cause)

  let index_of_lf_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc = Lf_variable { lf_level }; _ } ->
        let* lf_context_size = get_lf_context_size in
        return (lf_context_size - Lf_level.to_int lf_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_lf_term_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let index_of_lf_variable_opt = index_of_variable_opt index_of_lf_variable

  let index_of_meta_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc =
          Meta_variable { meta_level } | Contextual_variable { meta_level }
      ; _
      } ->
        let* meta_context_size = get_meta_context_size in
        return (meta_context_size - Meta_level.to_int meta_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_meta_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let index_of_meta_variable_opt =
    index_of_variable_opt index_of_meta_variable

  let index_of_parameter_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc =
          ( Parameter_variable { meta_level }
          | Contextual_variable { meta_level } )
      ; _
      } ->
        let* meta_context_size = get_meta_context_size in
        return (meta_context_size - Meta_level.to_int meta_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_parameter_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let index_of_parameter_variable_opt =
    index_of_variable_opt index_of_parameter_variable

  let index_of_substitution_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc =
          ( Substitution_variable { meta_level }
          | Contextual_variable { meta_level } )
      ; _
      } ->
        let* meta_context_size = get_meta_context_size in
        return (meta_context_size - Meta_level.to_int meta_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_substitution_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let index_of_substitution_variable_opt =
    index_of_variable_opt index_of_substitution_variable

  let index_of_context_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc =
          ( Context_variable { meta_level }
          | Contextual_variable { meta_level } )
      ; _
      } ->
        let* meta_context_size = get_meta_context_size in
        return (meta_context_size - Meta_level.to_int meta_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_context_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let index_of_context_variable_opt =
    index_of_variable_opt index_of_context_variable

  let index_of_comp_variable identifier =
    lookup_toplevel identifier >>= function
    | { desc = Computation_variable { comp_level }; _ } ->
        let* comp_context_size = get_comp_context_size in
        return (comp_context_size - Comp_level.to_int comp_level)
    | entry ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_computation_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))

  let with_free_variables_state ~free_variables_allowed m =
    let* state = get in
    let* () = put { state with free_variables_allowed } in
    let* x = m in
    let* state' = get in
    let* () =
      put
        { state' with free_variables_allowed = state.free_variables_allowed }
    in
    return x

  let allow_free_variables m =
    with_free_variables_state ~free_variables_allowed:true m

  let disallow_free_variables m =
    with_free_variables_state ~free_variables_allowed:false m

  let are_free_variables_allowed =
    let* state = get in
    return state.free_variables_allowed

  let add_free_variable ?location identifier adder =
    are_free_variables_allowed >>= function
    | false ->
        Error.raise_at1
          (Identifier.location identifier)
          Illegal_free_variable
    | true -> adder ?location identifier

  let shift_lf_context = modify_lf_context_size (( + ) 1)

  let unshift_lf_context = modify_lf_context_size (( - ) 1)

  let[@inline] with_shifted_lf_context m =
    shift_lf_context &> m <& unshift_lf_context

  let shift_meta_context = modify_meta_context_size (( + ) 1)

  let unshift_meta_context = modify_meta_context_size (( - ) 1)

  let[@inline] with_shifted_meta_context m =
    shift_meta_context &> m <& unshift_meta_context

  let shift_comp_context = modify_comp_context_size (( + ) 1)

  let unshift_comp_context = modify_comp_context_size (( - ) 1)

  let[@inline] with_shifted_comp_context m =
    shift_comp_context &> m <& unshift_comp_context

  let with_bindings_checkpoint m =
    let* bindings = get_bindings in
    let* x = m in
    let* () = set_bindings bindings in
    return x

  let binding_location ?location identifier =
    match location with
    | Option.Some binding_location -> binding_location
    | Option.None -> Identifier.location identifier

  let add_lf_level_variable ?location identifier make_entry =
    let binding_location = binding_location ?location identifier in
    modify_bindings_state (fun state ->
        let lf_context_size' = state.lf_context_size + 1 in
        let entry =
          make_entry binding_location (Lf_level.of_int lf_context_size')
        in
        let bindings' =
          Binding_tree.add_toplevel identifier entry state.bindings
        in
        { state with
          bindings = bindings'
        ; lf_context_size = lf_context_size'
        })

  let add_meta_level_variable ?location identifier make_entry =
    let binding_location = binding_location ?location identifier in
    modify_bindings_state (fun state ->
        let meta_context_size' = state.meta_context_size + 1 in
        let entry =
          make_entry binding_location (Meta_level.of_int meta_context_size')
        in
        let bindings' =
          Binding_tree.add_toplevel identifier entry state.bindings
        in
        { state with
          bindings = bindings'
        ; meta_context_size = meta_context_size'
        })

  let add_comp_level_variable ?location identifier make_entry =
    let binding_location = binding_location ?location identifier in
    modify_bindings_state (fun state ->
        let comp_context_size' = state.comp_context_size + 1 in
        let entry =
          make_entry binding_location (Comp_level.of_int comp_context_size')
        in
        let bindings' =
          Binding_tree.add_toplevel identifier entry state.bindings
        in
        { state with
          bindings = bindings'
        ; comp_context_size = comp_context_size'
        })

  let add_lf_variable ?location identifier =
    add_lf_level_variable ?location identifier
      (fun binding_location lf_level ->
        { binding_location; desc = Lf_variable { lf_level } })

  let add_meta_variable ?location identifier =
    add_meta_level_variable ?location identifier
      (fun binding_location meta_level ->
        { binding_location; desc = Meta_variable { meta_level } })

  let add_parameter_variable ?location identifier =
    add_meta_level_variable ?location identifier
      (fun binding_location meta_level ->
        { binding_location; desc = Parameter_variable { meta_level } })

  let add_substitution_variable ?location identifier =
    add_meta_level_variable ?location identifier
      (fun binding_location meta_level ->
        { binding_location; desc = Substitution_variable { meta_level } })

  let add_context_variable ?location identifier =
    add_meta_level_variable ?location identifier
      (fun binding_location meta_level ->
        { binding_location; desc = Context_variable { meta_level } })

  let add_contextual_variable ?location identifier =
    add_meta_level_variable ?location identifier
      (fun binding_location meta_level ->
        { binding_location; desc = Contextual_variable { meta_level } })

  let add_comp_variable ?location identifier =
    add_comp_level_variable ?location identifier
      (fun binding_location comp_level ->
        { binding_location; desc = Computation_variable { comp_level } })

  let with_bound_lf_variable ?location identifier m =
    with_bindings_checkpoint (add_lf_variable ?location identifier &> m)

  let with_bound_meta_variable ?location identifier m =
    with_bindings_checkpoint (add_meta_variable ?location identifier &> m)

  let with_bound_parameter_variable ?location identifier m =
    with_bindings_checkpoint
      (add_parameter_variable ?location identifier &> m)

  let with_bound_substitution_variable ?location identifier m =
    with_bindings_checkpoint
      (add_substitution_variable ?location identifier &> m)

  let with_bound_context_variable ?location identifier m =
    with_bindings_checkpoint (add_context_variable ?location identifier &> m)

  let with_bound_contextual_variable ?location identifier m =
    with_bindings_checkpoint
      (add_contextual_variable ?location identifier &> m)

  let with_bound_comp_variable ?location identifier m =
    with_bindings_checkpoint (add_comp_variable ?location identifier &> m)

  let add_lf_type_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Lf_type_constant { cid } }
          bindings)

  let add_lf_term_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Lf_term_constant { cid } }
          bindings)

  let add_schema_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Schema_constant { cid } }
          bindings)

  let add_inductive_computation_type_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location
          ; desc = Computation_inductive_type_constant { cid }
          }
          bindings)

  let add_stratified_computation_type_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location
          ; desc = Computation_stratified_type_constant { cid }
          }
          bindings)

  let add_coinductive_computation_type_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location
          ; desc = Computation_coinductive_type_constant { cid }
          }
          bindings)

  let add_abbreviation_computation_type_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location
          ; desc = Computation_abbreviation_type_constant { cid }
          }
          bindings)

  let add_computation_term_constructor ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Computation_term_constructor { cid } }
          bindings)

  let add_computation_term_destructor ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Computation_term_destructor { cid } }
          bindings)

  let add_program_constant ?location identifier cid =
    let binding_location = binding_location ?location identifier in
    modify_bindings (fun bindings ->
        Binding_tree.add_toplevel identifier
          { binding_location; desc = Program_constant { cid } }
          bindings)

  let start_module = Obj.magic () (* TODO: *)

  let stop_module ?location identifier cid = Obj.magic () (* TODO: *)

  let add_module ?location identifier cid m = Obj.magic () (* TODO: *)

  let with_scope m =
    let* state = get in
    let* bindings = get_bindings_state in
    let* () =
      put
        { state with
          substate =
            Scope_state { bindings; parent = Option.some state.substate }
        }
    in
    let* x = m in
    let* () = put state in
    return x

  let with_parent_scope m =
    let* state = get in
    match state.substate with
    | Scope_state { parent; _ } -> (
        match parent with
        | Option.Some parent ->
            let* () = put { state with substate = parent } in
            let* x = with_scope m in
            let* () = put state in
            return x
        | Option.None ->
            Error.raise_violation "[with_parent_scope] invalid state")
    | Pattern_state _ ->
        Error.raise_violation "[with_parent_scope] invalid state"

  let with_free_variables_as_pattern_variables ~pattern ~expression =
    Obj.magic () (* TODO: *)

  let add_computation_pattern_variable ?location identifier =
    Obj.magic () (* TODO: *)

  let add_free_lf_variable ?location identifier = Obj.magic () (* TODO: *)

  let add_free_meta_variable ?location identifier = Obj.magic () (* TODO: *)

  let add_free_parameter_variable ?location identifier =
    Obj.magic () (* TODO: *)

  let add_free_substitution_variable ?location identifier =
    Obj.magic () (* TODO: *)

  let add_free_context_variable ?location identifier =
    Obj.magic () (* TODO: *)

  let initial_state =
    { substate =
        Scope_state
          { bindings =
              { bindings = Binding_tree.empty
              ; lf_context_size = 0
              ; meta_context_size = 0
              ; comp_context_size = 0
              }
          ; parent = Option.none
          }
    ; free_variables_allowed = false
    ; generated_fresh_variables_count = 0
    }
end
