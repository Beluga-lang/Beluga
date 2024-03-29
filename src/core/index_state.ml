open Support
open Beluga_syntax.Syncom

[@@@warning "+A-4-44"]

exception Unbound_identifier = Identifier.Unbound_identifier

exception
  Unbound_qualified_identifier = Qualified_identifier
                                 .Unbound_qualified_identifier

exception Unbound_namespace = Qualified_identifier.Unbound_namespace

exception Bound_lf_type_constant of Qualified_identifier.t

exception Bound_lf_term_constant of Qualified_identifier.t

exception Bound_lf_variable of Qualified_identifier.t

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

exception Expected_constant

exception Expected_lf_typ_constant

exception Expected_lf_term_constant

exception Expected_schema_constant

exception Expected_computation_type_constant

exception Expected_computation_inductive_type_constant

exception Expected_computation_stratified_type_constant

exception Expected_computation_coinductive_type_constant

exception Expected_computation_abbreviation_type_constant

exception Expected_computation_term_constructor

exception Expected_computation_term_destructor

exception Expected_program_constant

exception Expected_module

exception Expected_lf_variable

exception Expected_meta_variable

exception Expected_parameter_variable

exception Expected_substitution_variable

exception Expected_context_variable

exception Expected_computation_variable

exception Illegal_free_lf_variable

exception Illegal_free_meta_variable

exception Illegal_free_parameter_variable

exception Illegal_free_substitution_variable

exception Illegal_free_context_variable

exception Illegal_free_computation_variable

exception Unknown_lf_variable_index

exception Unknown_meta_variable_index

exception Unknown_parameter_variable_index

exception Unknown_substitution_variable_index

exception Unknown_context_variable_index

exception Unknown_computation_variable_index

exception Duplicate_pattern_variables of Identifier.t List2.t

let () =
  Error.register_exception_printer (function
    | Bound_lf_type_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_term_constant qualified_identifier ->
        Format.dprintf "%a is a bound LF term constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_lf_variable qualified_identifier ->
        Format.dprintf "%a is a bound LF term variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_meta_variable qualified_identifier ->
        Format.dprintf "%a is a bound meta-variable." Qualified_identifier.pp
          qualified_identifier
    | Bound_parameter_variable qualified_identifier ->
        Format.dprintf "%a is a bound parameter variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_substitution_variable qualified_identifier ->
        Format.dprintf "%a is a bound substitution variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_context_variable qualified_identifier ->
        Format.dprintf "%a is a bound context variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_contextual_variable qualified_identifier ->
        Format.dprintf "%a is a bound contextual variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_schema_constant qualified_identifier ->
        Format.dprintf "%a is a bound schema constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_variable qualified_identifier ->
        Format.dprintf "%a is a bound computation variable."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_inductive_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level inductive type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_stratified_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level stratified type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_coinductive_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level coinductive type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_abbreviation_type_constant qualified_identifier ->
        Format.dprintf
          "%a is a bound computation-level abbreviation type constant."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_term_constructor qualified_identifier ->
        Format.dprintf "%a is a bound computation-level term constructor."
          Qualified_identifier.pp qualified_identifier
    | Bound_computation_term_destructor qualified_identifier ->
        Format.dprintf "%a is a bound computation-level term destructor."
          Qualified_identifier.pp qualified_identifier
    | Bound_module qualified_identifier ->
        Format.dprintf "%a is a bound module." Qualified_identifier.pp
          qualified_identifier
    | Bound_program_constant qualified_identifier ->
        Format.dprintf "%a is a bound program." Qualified_identifier.pp
          qualified_identifier
    | Expected_constant -> Format.dprintf "Expected a constant."
    | Expected_lf_typ_constant ->
        Format.dprintf "Expected an LF type-level constant."
    | Expected_lf_term_constant ->
        Format.dprintf "Expected an LF term-level constant."
    | Expected_schema_constant ->
        Format.dprintf "Expected a schema constant."
    | Expected_computation_type_constant ->
        Format.dprintf
          "Expected an inductive or stratified computation type constant."
    | Expected_computation_inductive_type_constant ->
        Format.dprintf "Expected an inductive computation type constant."
    | Expected_computation_stratified_type_constant ->
        Format.dprintf "Expected a stratified computation type constant."
    | Expected_computation_coinductive_type_constant ->
        Format.dprintf "Expected a coinductive computation type constant."
    | Expected_computation_abbreviation_type_constant ->
        Format.dprintf "Expected an abbreviation computation type constant."
    | Expected_computation_term_constructor ->
        Format.dprintf "Expected a computation constructor constant."
    | Expected_computation_term_destructor ->
        Format.dprintf "Expected a computation destructor constant."
    | Expected_program_constant ->
        Format.dprintf "Expected a computation program constant."
    | Expected_module -> Format.dprintf "Expected a module constant."
    | Expected_lf_variable -> Format.dprintf "Expected an LF variable."
    | Expected_meta_variable -> Format.dprintf "Expected a meta-variable."
    | Expected_parameter_variable ->
        Format.dprintf "Expected a parameter variable."
    | Expected_substitution_variable ->
        Format.dprintf "Expected a substitution variable."
    | Expected_context_variable ->
        Format.dprintf "Expected a context variable."
    | Expected_computation_variable ->
        Format.dprintf "Expected a computation-level variable."
    | Illegal_free_lf_variable ->
        Format.dprintf "This free LF variable is illegal."
    | Illegal_free_meta_variable ->
        Format.dprintf "This free meta-variable is illegal."
    | Illegal_free_parameter_variable ->
        Format.dprintf "This free parameter variable is illegal."
    | Illegal_free_substitution_variable ->
        Format.dprintf "This free substitution variable is illegal."
    | Illegal_free_context_variable ->
        Format.dprintf "This free context variable is illegal."
    | Illegal_free_computation_variable ->
        Format.dprintf "This free computation-level variable is illegal."
    | Unknown_lf_variable_index ->
        Format.dprintf
          "The de Bruijn index of this LF variable is unexpectedly unknown."
    | Unknown_meta_variable_index ->
        Format.dprintf
          "The de Bruijn index of this meta-variable is unexpectedly \
           unknown."
    | Unknown_parameter_variable_index ->
        Format.dprintf
          "The de Bruijn index of this parameter variable is unexpectedly \
           unknown."
    | Unknown_substitution_variable_index ->
        Format.dprintf
          "The de Bruijn index of this substitution variable is \
           unexpectedly unknown."
    | Unknown_context_variable_index ->
        Format.dprintf
          "The de Bruijn index of this context variable is unexpectedly \
           unknown."
    | Unknown_computation_variable_index ->
        Format.dprintf
          "The de Bruijn index of this computation variable is unexpectedly \
           unknown."
    | Duplicate_pattern_variables _ ->
        Format.dprintf "Illegal duplicate pattern variables."
    | exn -> Error.raise_unsupported_exception_printing exn)

(** Abstract definition of de Bruijn levels.

    A de Bruin level indexes a variable from the bottom of the context when
    viewed as a stack. In other words, the de Bruin level of a variable in a
    context represented as a list is the 0-based index of that variable in
    the list.

    If variable [x] has de Bruijn level [l] in a context [psi], then the de
    Bruijn index of [x] is [length(psi) - l]. *)
module type LEVEL = sig
  type t

  val of_int : Int.t -> t

  val to_int : t -> Int.t
end

(** Concrete definition of de Bruijn levels. *)
module Level = struct
  type t = int

  let of_int = Fun.id

  let to_int = Fun.id
end

(** Concrete definition of de Bruijn levels for the context of LF-bound
    variables.

    The context of LF-bound variables is typically denoted [cPsi]. If
    variable [x] is in [cPsi] with level [l], then the de Bruijn index of [x]
    is [length(cPsi) - l]. *)
module Lf_level : LEVEL = Level

(** Concrete definition of de Bruijn levels for the context of meta-level
    bound variables.

    The context of meta-level bound variables is typically denoted [cD]. If
    variable [x] is in [cD] with level [l], then the de Bruijn index of [x]
    is [length(cD) - l]. *)
module Meta_level : LEVEL = Level

(** Concrete definition of de Bruijn levels for the context of
    computation-level bound variables.

    The context of computation-level bound variables is typically denoted
    [cG]. If variable [x] is in [cG] with level [l], then the de Bruijn index
    of [x] is [length(cG) - l]. *)
module Comp_level : LEVEL = Level

(** Concrete definition of entries in the store for indexing.

    Variables are stored with their associated de Bruijn level because
    variables in [cPsi], [cD] and [cG] share the same namespace. This avoids
    explicitly representing those contexts as lists. Additionally, we do not
    have to pollute the namespace with fresh variables generated for binders
    that omit their identifier, like the LF term-level abstraction [\_. x]. *)
module Entry = struct
  type t =
    { binding_location : Location.t
    ; desc : desc
    }

  and desc =
    | Lf_variable of
        { lf_level : Lf_level.t Option.t
              (** The de Bruijn level of the LF variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
    | Meta_variable of
        { meta_level : Meta_level.t Option.t
              (** The de Bruijn level of the meta-variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
    | Parameter_variable of
        { meta_level : Meta_level.t Option.t
              (** The de Bruijn level of the parameter variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
    | Substitution_variable of
        { meta_level : Meta_level.t Option.t
              (** The de Bruijn level of the substitution variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
    | Context_variable of
        { meta_level : Meta_level.t Option.t
              (** The de Bruijn level of the context variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
    | Contextual_variable of
        { meta_level : Meta_level.t Option.t
              (** The de Bruijn level of the contextual variable. If it is
                  [Option.None], then this is a free variable, whose level is
                  unknown. *)
        }
        (** A contextual variable is either a meta, parameter, substitution,
            or context variable. Contextual variables are introduced
            ambiguously by [mlam]-expressions. *)
    | Computation_variable of
        { comp_level : Comp_level.t Option.t
              (** The de Bruijn level of the computation-level variable. If
                  it is [Option.None], then this is a free variable, whose
                  level is unknown. *)
        }
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

  let[@inline] binding_location ?location identifier =
    match location with
    | Option.Some binding_location -> binding_location
    | Option.None -> Identifier.location identifier

  let[@inline] make_entry ?location identifier desc =
    let binding_location = binding_location ?location identifier in
    { binding_location; desc }

  let[@inline] make_lf_variable_entry ?location identifier ~lf_level =
    make_entry ?location identifier (Lf_variable { lf_level })

  let[@inline] make_meta_variable_entry ?location identifier ~meta_level =
    make_entry ?location identifier (Meta_variable { meta_level })

  let[@inline] make_parameter_variable_entry ?location identifier ~meta_level
      =
    make_entry ?location identifier (Parameter_variable { meta_level })

  let[@inline] make_substitution_variable_entry ?location identifier
      ~meta_level =
    make_entry ?location identifier (Substitution_variable { meta_level })

  let[@inline] make_context_variable_entry ?location identifier ~meta_level =
    make_entry ?location identifier (Context_variable { meta_level })

  let[@inline] make_contextual_variable_entry ?location identifier
      ~meta_level =
    make_entry ?location identifier (Contextual_variable { meta_level })

  let[@inline] make_computation_variable_entry ?location identifier
      ~comp_level =
    make_entry ?location identifier (Computation_variable { comp_level })

  let[@inline] make_lf_type_constant_entry ?location identifier cid =
    make_entry ?location identifier (Lf_type_constant { cid })

  let[@inline] make_lf_term_constant_entry ?location identifier cid =
    make_entry ?location identifier (Lf_term_constant { cid })

  let[@inline] make_schema_constant_entry ?location identifier cid =
    make_entry ?location identifier (Schema_constant { cid })

  let[@inline] make_computation_inductive_type_constant_entry ?location
      identifier cid =
    make_entry ?location identifier
      (Computation_inductive_type_constant { cid })

  let[@inline] make_computation_stratified_type_constant_entry ?location
      identifier cid =
    make_entry ?location identifier
      (Computation_stratified_type_constant { cid })

  let[@inline] make_computation_coinductive_type_constant_entry ?location
      identifier cid =
    make_entry ?location identifier
      (Computation_coinductive_type_constant { cid })

  let[@inline] make_computation_abbreviation_type_constant_entry ?location
      identifier cid =
    make_entry ?location identifier
      (Computation_abbreviation_type_constant { cid })

  let[@inline] make_computation_term_constructor_entry ?location identifier
      cid =
    make_entry ?location identifier (Computation_term_constructor { cid })

  let[@inline] make_computation_term_destructor_entry ?location identifier
      cid =
    make_entry ?location identifier (Computation_term_destructor { cid })

  let[@inline] make_program_constant_entry ?location identifier cid =
    make_entry ?location identifier (Program_constant { cid })

  let[@inline] make_module_entry ?location identifier cid =
    make_entry ?location identifier (Module { cid })

  let actual_binding_exn identifier { binding_location; desc } =
    Error.located_exception1 binding_location
      (match desc with
      | Lf_variable _ -> Bound_lf_variable identifier
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

  let is_variable entry =
    match entry.desc with
    | Lf_variable _
    | Meta_variable _
    | Parameter_variable _
    | Substitution_variable _
    | Context_variable _
    | Contextual_variable _
    | Computation_variable _ ->
        true
    | Lf_type_constant _
    | Lf_term_constant _
    | Schema_constant _
    | Computation_inductive_type_constant _
    | Computation_stratified_type_constant _
    | Computation_coinductive_type_constant _
    | Computation_abbreviation_type_constant _
    | Computation_term_constructor _
    | Computation_term_destructor _
    | Program_constant _
    | Module _ ->
        false
end

module type INDEXING_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val fresh_identifier : state -> Identifier.t

  val fresh_identifier_opt : state -> Identifier.t Option.t -> Identifier.t

  val index_of_constant :
       state
    -> Qualified_identifier.t
    -> [ `Lf_type_constant of Id.cid_typ
       | `Lf_term_constant of Id.cid_term
       | `Computation_inductive_type_constant of Id.cid_comp_typ
       | `Computation_stratified_type_constant of Id.cid_comp_typ
       | `Computation_coinductive_type_constant of Id.cid_comp_cotyp
       | `Computation_abbreviation_type_constant of Id.cid_comp_typdef
       | `Computation_term_constructor of Id.cid_comp_const
       | `Computation_term_destructor of Id.cid_comp_dest
       | `Schema_constant of Id.cid_schema
       | `Program_constant of Id.cid_prog
       | `Module of Id.module_id
       ]

  val index_of_lf_type_constant :
    state -> Qualified_identifier.t -> Id.cid_typ

  val index_of_lf_term_constant :
    state -> Qualified_identifier.t -> Id.cid_term

  val index_of_comp_type_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val index_of_inductive_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val index_of_stratified_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typ

  val index_of_coinductive_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_cotyp

  val index_of_abbreviation_comp_constant :
    state -> Qualified_identifier.t -> Id.cid_comp_typdef

  val index_of_schema_constant :
    state -> Qualified_identifier.t -> Id.cid_schema

  val index_of_comp_constructor :
    state -> Qualified_identifier.t -> Id.cid_comp_const

  val index_of_comp_destructor :
    state -> Qualified_identifier.t -> Id.cid_comp_dest

  val index_of_comp_program : state -> Qualified_identifier.t -> Id.cid_prog

  val index_of_lf_variable : state -> Identifier.t -> Id.offset

  val index_of_lf_variable_opt : state -> Identifier.t -> Id.offset Option.t

  val index_of_meta_variable : state -> Identifier.t -> Id.offset

  val index_of_meta_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_parameter_variable : state -> Identifier.t -> Id.offset

  val index_of_parameter_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_substitution_variable : state -> Identifier.t -> Id.offset

  val index_of_substitution_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_context_variable : state -> Identifier.t -> Id.offset

  val index_of_context_variable_opt :
    state -> Identifier.t -> Id.offset Option.t

  val index_of_comp_variable : state -> Identifier.t -> Id.offset

  val with_bound_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_contextual_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_comp_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_shifted_lf_context : state -> (state -> 'a) -> 'a

  val with_shifted_meta_context : state -> (state -> 'a) -> 'a

  val with_shifted_comp_context : state -> (state -> 'a) -> 'a

  val add_lf_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t

  val add_inductive_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_stratified_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_coinductive_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_cotyp
    -> Unit.t

  val add_abbreviation_computation_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typdef
    -> Unit.t

  val add_computation_term_constructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_const
    -> Unit.t

  val add_computation_term_destructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_dest
    -> Unit.t

  val add_program_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val add_module :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.module_id
    -> (state -> 'a)
    -> 'a

  val open_module :
    state -> ?location:Location.t -> Qualified_identifier.t -> Unit.t

  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> Identifier.t
    -> Unit.t

  val with_frame : state -> (state -> 'a) -> 'a

  val with_parent_frame : state -> (state -> 'a) -> 'a

  val with_bindings_checkpoint : state -> (state -> 'a) -> 'a

  val with_free_variables_as_pattern_variables :
    state -> pattern:(state -> 'a) -> expression:(state -> 'a -> 'b) -> 'b

  val add_computation_pattern_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_lf_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val add_free_context_variable :
    state -> ?location:Location.t -> Identifier.t -> Unit.t

  val with_bound_pattern_meta_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_parameter_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_substitution_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val with_bound_pattern_context_variable :
    state -> ?location:Location.t -> Identifier.t -> (state -> 'a) -> 'a

  val allow_free_variables : state -> (state -> 'a) -> 'a

  val disallow_free_variables : state -> (state -> 'a) -> 'a

  val add_all_mctx : state -> Synint.LF.mctx -> Unit.t

  val add_all_gctx : state -> Synint.Comp.gctx -> Unit.t
end

module Indexing_state = struct
  type entry_binding_tree = Entry.t Binding_tree.t

  type bindings =
    { bindings : entry_binding_tree
    ; mutable lf_context_size : Int.t
          (** The length of [cPsi], the context of LF-bound variables. *)
    ; mutable meta_context_size : Int.t
          (** The length of [cD], the context of meta-level variables. *)
    ; mutable comp_context_size : Int.t
          (** The length of [cG], the context of computation-level variables. *)
    }

  type frame =
    | Plain_frame of { bindings : bindings }
    | Pattern_frame of
        { pattern_bindings : bindings
        ; mutable pattern_variables_rev : Identifier.t List.t
        ; expression_bindings : bindings
        }
    | Module_frame of
        { bindings : bindings
        ; declarations : entry_binding_tree
        }

  type state =
    { mutable frames : frame List1.t
    ; mutable free_variables_allowed : Bool.t
    ; mutable generated_fresh_variables_count : Int.t
    }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let[@inline] create_empty_bindings () =
    { bindings = Binding_tree.create ()
    ; lf_context_size = 0
    ; meta_context_size = 0
    ; comp_context_size = 0
    }

  let[@inline] create_empty_module_frame () =
    Module_frame
      { bindings = create_empty_bindings ()
      ; declarations = Binding_tree.create ()
      }

  let[@inline] create_initial_state () =
    { frames = List1.singleton (create_empty_module_frame ())
    ; free_variables_allowed = false
    ; generated_fresh_variables_count = 0
    }

  let clear_state state =
    state.frames <- List1.singleton (create_empty_module_frame ());
    state.free_variables_allowed <- false;
    state.generated_fresh_variables_count <- 0

  let[@inline] enable_free_variables state =
    state.free_variables_allowed <- true

  let[@inline] disable_free_variables state =
    state.free_variables_allowed <- false

  let[@inline] set_free_variables_allowed_state state free_variables_allowed
      =
    state.free_variables_allowed <- free_variables_allowed

  let[@inline] are_free_variables_allowed state =
    state.free_variables_allowed

  let fresh_identifier state =
    let i = state.generated_fresh_variables_count in
    state.generated_fresh_variables_count <- i + 1;
    (* ['"'] is a reserved character, so ["\"i1"], ["\"i2"], ..., etc. are
       syntactically invalid identifiers, which are guaranteed to not clash
       with free variables. *)
    Identifier.make ("\"i" ^ string_of_int i)

  let fresh_identifier_opt state = function
    | Option.Some identifier -> identifier
    | Option.None -> fresh_identifier state

  let[@inline] get_frame_bindings_state = function
    | Pattern_frame { pattern_bindings = bindings; _ }
    | Module_frame { bindings; _ }
    | Plain_frame { bindings } ->
        bindings

  let[@inline] get_frame_bindings state =
    (get_frame_bindings_state state).bindings

  let[@inline] push_frame state frame =
    state.frames <- List1.cons frame state.frames

  let pop_frame state =
    match state.frames with
    | List1.T (x1, x2 :: xs) ->
        state.frames <- List1.from x2 xs;
        x1
    | List1.T (_x, []) ->
        (* This suggests a mismanaged frames state, where there are more
           [pop_frame] operations than there are [push_frame] operations. *)
        Error.raise_violation
          (Format.asprintf "[%s] cannot pop the last frame" __FUNCTION__)

  let[@inline] get_current_frame state = List1.head state.frames

  let[@inline] get_current_frame_bindings_state state =
    get_frame_bindings_state (get_current_frame state)

  let[@inline] get_current_frame_bindings state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    current_frame_bindings_state.bindings

  (** [push_new_plain_frame state] pushes a new empty plain frame to [state].
      The LF, meta and computation context sizes are carried over. *)
  let push_new_plain_frame state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    let bindings =
      { bindings = Binding_tree.create ()
      ; lf_context_size = current_frame_bindings_state.lf_context_size
      ; meta_context_size = current_frame_bindings_state.meta_context_size
      ; comp_context_size = current_frame_bindings_state.comp_context_size
      }
    in
    let frame = Plain_frame { bindings } in
    push_frame state frame

  let entry_is_not_variable entry = Bool.not (Entry.is_variable entry)

  let lookup_toplevel_in_frame frame query =
    Binding_tree.lookup_toplevel_opt query (get_frame_bindings frame)

  let lookup_toplevel_in_frames frames query =
    List.find_map (fun frame -> lookup_toplevel_in_frame frame query) frames

  let rec lookup_toplevel_declaration_in_frames frames query =
    match frames with
    | [] -> (* Exhausted the list of frames to check. *) Option.none
    | frame :: frames -> (
        let frame_bindings = get_frame_bindings frame in
        match Binding_tree.lookup_toplevel_opt query frame_bindings with
        | Option.Some (entry, subtree) when entry_is_not_variable entry ->
            (* [query] is bound to a declaration in [frame]. *)
            Option.some (entry, subtree)
        | Option.Some _ ->
            (* [query] is bound to a variable in [frame], so any declaration
               in [frames] bound to [query] is shadowed. *)
            Option.none
        | Option.None ->
            (* [query] is unbound in [frame], so check in the parent
               frames. *)
            lookup_toplevel_declaration_in_frames frames query)

  (** [lookup_toplevel_opt state query] is the entry and subtree bound to the
      identifier [query] in [state]. The "toplevel" here refers to [query]
      not being a qualified identifier, meaning that we do not have to
      perform traversals in namespaces. To lookup qualified identifiers, see
      {!val:lookup}.

      The entry bound to [query] in [state] is the first entry found in a
      frame in the stack of frames in [state].

      Exceptionally for pattern frames, we ignore bound variables in outer
      frames. This means that in the computation-level Beluga expression
      [let x = ? in case ? of p => ?], the pattern [p] may not refer to [x].
      The name [x] can be used in [p], but it is considered a free variable. *)
  let lookup_toplevel_opt state query =
    match state.frames with
    | List1.T ((Pattern_frame _ as frame), frames) -> (
        match lookup_toplevel_in_frame frame query with
        | Option.Some x -> Option.some x
        | Option.None -> lookup_toplevel_declaration_in_frames frames query)
    | List1.T (frame, frames) ->
        lookup_toplevel_in_frames (frame :: frames) query

  let rec lookup_in_frames frames identifiers =
    match frames with
    | [] ->
        Error.raise
          (Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | frame :: frames -> (
        match
          Binding_tree.maximum_lookup identifiers (get_frame_bindings frame)
        with
        | Binding_tree.Bound { entry; subtree; _ } -> (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ -> lookup_in_frames frames identifiers)

  let rec lookup_declaration_in_frames frames identifiers =
    match frames with
    | [] ->
        Error.raise
          (Unbound_qualified_identifier
             (Qualified_identifier.from_list1 identifiers))
    | frame :: frames -> (
        let frame_bindings = get_frame_bindings frame in
        match Binding_tree.maximum_lookup identifiers frame_bindings with
        | Binding_tree.Bound { entry; subtree; _ }
          when entry_is_not_variable entry ->
            (* [query] is bound to a declaration in [frame]. *)
            (entry, subtree)
        | Binding_tree.Bound _result ->
            (* [query is bound to a variable in [frame], so any declaration
               in [frames] bound to [query] is shadowed. *)
            assert (List1.length identifiers = 1)
            (* Variables can't be in namespaces *);
            Error.raise
              (Unbound_qualified_identifier
                 (Qualified_identifier.from_list1 identifiers))
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ ->
            lookup_declaration_in_frames frames identifiers)

  (** [lookup state query] is the entry and subtree bound to the qualified
      identifier [query] in [state]. To lookup simple identifiers, see
      {!val:lookup_toplevel}.

      The entry bound to [query] in [state] is the first entry found in a
      frame in the stack of frames in [state]. If a frame has [entry] as
      partially bound (meaning that only the first few namespaces of [query]
      are bound in that frame), then [query] is considered to be unbound
      because one of its namespaces is unbound. *)
  let lookup state query =
    let identifiers = Qualified_identifier.to_list1 query in
    match state.frames with
    | List1.T ((Pattern_frame _ as frame), frames) -> (
        match
          Binding_tree.maximum_lookup identifiers (get_frame_bindings frame)
        with
        | Binding_tree.Bound { entry; subtree; _ } -> (entry, subtree)
        | Binding_tree.Partially_bound { leading_segments; segment; _ } ->
            Error.raise
              (Unbound_namespace
                 (Qualified_identifier.make ~namespaces:leading_segments
                    segment))
        | Binding_tree.Unbound _ ->
            lookup_declaration_in_frames frames identifiers)
    | List1.T (frame, frames) ->
        lookup_in_frames (frame :: frames) identifiers

  let add_binding state identifier ?subtree entry =
    match get_current_frame state with
    | Plain_frame { bindings }
    | Pattern_frame { pattern_bindings = bindings; _ }
    | Module_frame { bindings; _ } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings.bindings

  let[@inline] increment_lf_context_size bindings =
    bindings.lf_context_size <- bindings.lf_context_size + 1

  let[@inline] decrement_lf_context_size bindings =
    bindings.lf_context_size <- bindings.lf_context_size - 1

  let[@inline] increment_meta_context_size bindings =
    bindings.meta_context_size <- bindings.meta_context_size + 1

  let[@inline] decrement_meta_context_size bindings =
    bindings.meta_context_size <- bindings.meta_context_size - 1

  let[@inline] increment_comp_context_size bindings =
    bindings.comp_context_size <- bindings.comp_context_size + 1

  let[@inline] decrement_comp_context_size bindings =
    bindings.comp_context_size <- bindings.comp_context_size - 1

  (** [remove_lf_binding state identifier] removes the latest binding of
      [identifier] from [state]. It is assumed that this binding is that of
      an LF variable, and that it was introduced in the current frame. *)
  let remove_lf_binding state identifier =
    match get_current_frame state with
    | Plain_frame { bindings }
    | Pattern_frame { pattern_bindings = bindings; _ }
    | Module_frame { bindings; _ } ->
        Binding_tree.remove identifier bindings.bindings;
        decrement_lf_context_size bindings

  (** [remove_meta_binding state identifier] removes the latest binding of
      [identifier] from [state]. It is assumed that this binding is that of a
      meta-level variable, and that it was introduced in the current frame. *)
  let remove_meta_binding state identifier =
    match get_current_frame state with
    | Plain_frame { bindings }
    | Pattern_frame { pattern_bindings = bindings; _ }
    | Module_frame { bindings; _ } ->
        Binding_tree.remove identifier bindings.bindings;
        decrement_meta_context_size bindings

  (** [remove_comp_binding state identifier] removes the latest binding of
      [identifier] from [state]. It is assumed that this binding is that of a
      computation-level variable, and that it was introduced in the current
      frame. *)
  let remove_comp_binding state identifier =
    match get_current_frame state with
    | Plain_frame { bindings }
    | Pattern_frame { pattern_bindings = bindings; _ }
    | Module_frame { bindings; _ } ->
        Binding_tree.remove identifier bindings.bindings;
        decrement_comp_context_size bindings

  let add_declaration state identifier ?subtree entry =
    match get_current_frame state with
    | Plain_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid plain frame, expected a module frame" __FUNCTION__)
    | Pattern_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid pattern frame, expected a module frame"
             __FUNCTION__)
    | Module_frame { bindings; declarations } ->
        Binding_tree.add_toplevel identifier entry ?subtree bindings.bindings;
        Binding_tree.add_toplevel identifier entry ?subtree declarations

  let add_lf_level_variable state identifier make_entry =
    let bindings = get_current_frame_bindings_state state in
    let entry =
      make_entry
        ~lf_level:(Option.some (Lf_level.of_int bindings.lf_context_size))
    in
    increment_lf_context_size bindings;
    Binding_tree.add_toplevel identifier entry bindings.bindings

  let add_meta_level_variable state identifier make_entry =
    let bindings = get_current_frame_bindings_state state in
    let entry =
      make_entry
        ~meta_level:
          (Option.some (Meta_level.of_int bindings.meta_context_size))
    in
    increment_meta_context_size bindings;
    Binding_tree.add_toplevel identifier entry bindings.bindings

  let add_comp_level_variable state identifier make_entry =
    let bindings = get_current_frame_bindings_state state in
    let entry =
      make_entry
        ~comp_level:
          (Option.some (Comp_level.of_int bindings.comp_context_size))
    in
    increment_comp_context_size bindings;
    Binding_tree.add_toplevel identifier entry bindings.bindings

  let add_lf_variable state ?location identifier =
    add_lf_level_variable state identifier
      (Entry.make_lf_variable_entry ?location identifier)

  let add_meta_variable state ?location identifier =
    add_meta_level_variable state identifier
      (Entry.make_meta_variable_entry ?location identifier)

  let add_parameter_variable state ?location identifier =
    add_meta_level_variable state identifier
      (Entry.make_parameter_variable_entry ?location identifier)

  let add_substitution_variable state ?location identifier =
    add_meta_level_variable state identifier
      (Entry.make_substitution_variable_entry ?location identifier)

  let add_context_variable state ?location identifier =
    add_meta_level_variable state identifier
      (Entry.make_context_variable_entry ?location identifier)

  let add_contextual_variable state ?location identifier =
    add_meta_level_variable state identifier
      (Entry.make_contextual_variable_entry ?location identifier)

  let add_comp_variable state ?location identifier =
    add_comp_level_variable state identifier
      (Entry.make_computation_variable_entry ?location identifier)

  let shift_lf_context state =
    let bindings_state = get_current_frame_bindings_state state in
    increment_lf_context_size bindings_state

  let unshift_lf_context state =
    let bindings_state = get_current_frame_bindings_state state in
    decrement_lf_context_size bindings_state

  let shift_meta_context state =
    let bindings_state = get_current_frame_bindings_state state in
    increment_meta_context_size bindings_state

  let unshift_meta_context state =
    let bindings_state = get_current_frame_bindings_state state in
    decrement_meta_context_size bindings_state

  let shift_comp_context state =
    let bindings_state = get_current_frame_bindings_state state in
    increment_comp_context_size bindings_state

  let unshift_comp_context state =
    let bindings_state = get_current_frame_bindings_state state in
    decrement_comp_context_size bindings_state

  let actual_binding_exn = Entry.actual_binding_exn

  let index_of_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Lf_type_constant { cid }; _ }, _ ->
        `Lf_type_constant cid
    | { Entry.desc = Entry.Lf_term_constant { cid }; _ }, _ ->
        `Lf_term_constant cid
    | ( { Entry.desc = Entry.Computation_inductive_type_constant { cid }; _ }
      , _ ) ->
        `Computation_inductive_type_constant cid
    | ( { Entry.desc = Entry.Computation_stratified_type_constant { cid }; _ }
      , _ ) ->
        `Computation_stratified_type_constant cid
    | ( { Entry.desc = Entry.Computation_coinductive_type_constant { cid }
        ; _
        }
      , _ ) ->
        `Computation_coinductive_type_constant cid
    | ( { Entry.desc = Entry.Computation_abbreviation_type_constant { cid }
        ; _
        }
      , _ ) ->
        `Computation_abbreviation_type_constant cid
    | { Entry.desc = Entry.Schema_constant { cid }; _ }, _ ->
        `Schema_constant cid
    | { Entry.desc = Entry.Computation_term_constructor { cid }; _ }, _ ->
        `Computation_term_constructor cid
    | { Entry.desc = Entry.Computation_term_destructor { cid }; _ }, _ ->
        `Computation_term_destructor cid
    | { Entry.desc = Entry.Program_constant { cid }; _ }, _ ->
        `Program_constant cid
    | { Entry.desc = Entry.Module { cid }; _ }, _ -> `Module cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_constant
             (actual_binding_exn qualified_identifier entry))
    | exception exn ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          exn

  let index_of_lf_type_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Lf_type_constant { cid }; _ }, _ -> cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_lf_typ_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_lf_term_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Lf_term_constant { cid }; _ }, _ -> cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_lf_term_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_type_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | ( { Entry.desc =
            ( Entry.Computation_inductive_type_constant { cid }
            | Entry.Computation_stratified_type_constant { cid } )
        ; _
        }
      , _ ) ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_computation_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_inductive_comp_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | ( { Entry.desc = Entry.Computation_inductive_type_constant { cid }; _ }
      , _ ) ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_inductive_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_stratified_comp_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | ( { Entry.desc = Entry.Computation_stratified_type_constant { cid }; _ }
      , _ ) ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_stratified_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_coinductive_comp_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | ( { Entry.desc = Entry.Computation_coinductive_type_constant { cid }
        ; _
        }
      , _ ) ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_coinductive_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_abbreviation_comp_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | ( { Entry.desc = Entry.Computation_abbreviation_type_constant { cid }
        ; _
        }
      , _ ) ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2
             Expected_computation_abbreviation_type_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_schema_constant state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Schema_constant { cid }; _ }, _ -> cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_schema_constant
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_constructor state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Computation_term_constructor { cid }; _ }, _ ->
        cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_computation_term_constructor
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_destructor state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Computation_term_destructor { cid }; _ }, _ -> cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_computation_term_destructor
             (actual_binding_exn qualified_identifier entry))

  let index_of_comp_program state qualified_identifier =
    match lookup state qualified_identifier with
    | { Entry.desc = Entry.Program_constant { cid }; _ }, _ -> cid
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location qualified_identifier)
          (Error.composite_exception2 Expected_program_constant
             (actual_binding_exn qualified_identifier entry))

  let[@inline] get_lf_context_size state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    current_frame_bindings_state.lf_context_size

  let[@inline] get_meta_context_size state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    current_frame_bindings_state.meta_context_size

  let[@inline] get_comp_context_size state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    current_frame_bindings_state.comp_context_size

  let[@inline] index_of_lf_level state lf_level =
    let lf_context_size = get_lf_context_size state in
    lf_context_size - Lf_level.to_int lf_level

  let[@inline] index_of_meta_level state meta_level =
    let meta_context_size = get_meta_context_size state in
    meta_context_size - Meta_level.to_int meta_level

  let[@inline] index_of_comp_level state comp_level =
    let comp_context_size = get_comp_context_size state in
    comp_context_size - Comp_level.to_int comp_level

  let index_of_lf_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some ({ Entry.desc = Entry.Lf_variable { lf_level }; _ }, _)
      -> (
        match lf_level with
        | Option.Some lf_level -> index_of_lf_level state lf_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_lf_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_lf_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let index_of_lf_variable_opt state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some ({ Entry.desc = Entry.Lf_variable { lf_level }; _ }, _)
      -> (
        match lf_level with
        | Option.Some lf_level ->
            Option.some (index_of_lf_level state lf_level)
        | Option.None -> Option.none)
    | Option.Some _
    | Option.None ->
        Option.none

  let index_of_meta_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Meta_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level -> index_of_meta_level state meta_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_meta_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_meta_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let index_of_meta_variable_opt state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Meta_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level ->
            Option.some (index_of_meta_level state meta_level)
        | Option.None -> Option.none)
    | Option.Some _
    | Option.None ->
        Option.none

  let index_of_parameter_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Parameter_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level -> index_of_meta_level state meta_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_parameter_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_parameter_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let index_of_parameter_variable_opt state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Parameter_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level ->
            Option.some (index_of_meta_level state meta_level)
        | Option.None -> Option.none)
    | Option.Some _
    | Option.None ->
        Option.none

  let index_of_substitution_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Substitution_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level -> index_of_meta_level state meta_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_substitution_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_substitution_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let index_of_substitution_variable_opt state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Substitution_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level ->
            Option.some (index_of_meta_level state meta_level)
        | Option.None -> Option.none)
    | Option.Some _
    | Option.None ->
        Option.none

  let index_of_context_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Context_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level -> index_of_meta_level state meta_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_context_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_context_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let index_of_context_variable_opt state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              ( Entry.Context_variable { meta_level }
              | Entry.Contextual_variable { meta_level } )
          ; _
          }
        , _ ) -> (
        match meta_level with
        | Option.Some meta_level ->
            Option.some (index_of_meta_level state meta_level)
        | Option.None -> Option.none)
    | Option.Some _
    | Option.None ->
        Option.none

  let index_of_comp_variable state identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ({ Entry.desc = Entry.Computation_variable { comp_level }; _ }, _)
      -> (
        match comp_level with
        | Option.Some comp_level -> index_of_comp_level state comp_level
        | Option.None ->
            Error.raise_at1
              (Identifier.location identifier)
              Unknown_computation_variable_index)
    | Option.Some (entry, _) ->
        Error.raise_at1
          (Identifier.location identifier)
          (Error.composite_exception2 Expected_computation_variable
             (actual_binding_exn
                (Qualified_identifier.make_simple identifier)
                entry))
    | Option.None ->
        Error.raise_at1
          (Identifier.location identifier)
          (Unbound_identifier identifier)

  let open_namespace state identifier =
    let _entry, subtree = lookup state identifier in
    let bindings = get_current_frame_bindings state in
    Binding_tree.add_all bindings subtree

  let open_module state ?location identifier =
    match lookup state identifier with
    | { Entry.desc = Entry.Module _; _ }, _ ->
        open_namespace state identifier
    | entry, _ ->
        Error.raise_at1_opt location
          (Error.composite_exception2 Expected_module
             (actual_binding_exn identifier entry))

  let add_synonym state ?location qualified_identifier synonym =
    let entry, subtree = lookup state qualified_identifier in
    let binding_location' =
      match location with
      | Option.None -> entry.Entry.binding_location
      | Option.Some location -> location
    in
    let entry' = Entry.{ entry with binding_location = binding_location' } in
    add_binding state synonym ~subtree entry'

  let add_module_abbreviation state ?location module_identifier abbreviation
      =
    match lookup state module_identifier with
    | { Entry.desc = Entry.Module _; _ }, _ ->
        add_synonym state ?location module_identifier abbreviation
    | entry, _ ->
        Error.raise_at1
          (Qualified_identifier.location module_identifier)
          (Error.composite_exception2 Expected_module
             (actual_binding_exn module_identifier entry))

  let raise_duplicate_identifiers_exception f duplicates =
    match duplicates with
    | List1.T ((_identifier, duplicates), []) ->
        Error.raise_at
          (List2.to_list1 (List2.map Identifier.location duplicates))
          (f duplicates)
    | List1.T (x1, x2 :: xs) ->
        Error.raise_aggregate_exception
          (List2.map
             (fun (_identifier, duplicates) ->
               Error.located_exception
                 (List2.to_list1 (List2.map Identifier.location duplicates))
                 (f duplicates))
             (List2.from x1 x2 xs))

  let add_free_lf_level_variable _state _identifier _make_entry = ()

  let add_free_meta_level_variable state identifier make_entry =
    match get_current_frame state with
    | Pattern_frame frame ->
        let entry = make_entry ~meta_level:Option.none in
        frame.pattern_variables_rev <-
          identifier :: frame.pattern_variables_rev;
        Binding_tree.add_toplevel identifier entry
          frame.pattern_bindings.bindings;
        Binding_tree.add_toplevel identifier entry
          frame.expression_bindings.bindings
    | Plain_frame _
    | Module_frame _ ->
        ()

  let add_free_comp_level_variable state identifier make_entry =
    match get_current_frame state with
    | Pattern_frame frame ->
        let entry =
          make_entry
            ~comp_level:
              (Option.some
                 (Comp_level.of_int
                    frame.expression_bindings.comp_context_size))
        in
        frame.pattern_variables_rev <-
          identifier :: frame.pattern_variables_rev;
        Binding_tree.add_toplevel identifier entry
          frame.expression_bindings.bindings;
        increment_comp_context_size frame.expression_bindings
    | Plain_frame _
    | Module_frame _ ->
        ()

  let add_free_lf_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ({ Entry.desc = Entry.Lf_variable { lf_level = Option.None }; _ }, _)
      ->
        (* [identifier] is known to be a free LF variable because its LF de
           Bruijn level is unknown, so we do not signal it as an illegal free
           variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_lf_level_variable state identifier
            (Entry.make_lf_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_lf_variable

  let add_free_meta_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc = Entry.Meta_variable { meta_level = Option.None }; _ }
        , _ ) ->
        (* [identifier] is known to be a free meta-variable because its meta
           de Bruijn level is unknown, so we do not signal it as an illegal
           free variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_meta_level_variable state identifier
            (Entry.make_meta_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_meta_variable

  let add_free_parameter_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc = Entry.Parameter_variable { meta_level = Option.None }
          ; _
          }
        , _ ) ->
        (* [identifier] is known to be a free parameter variable because its
           meta de Bruijn level is unknown, so we do not signal it as an
           illegal free variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_meta_level_variable state identifier
            (Entry.make_parameter_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_parameter_variable

  let add_free_substitution_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              Entry.Substitution_variable { meta_level = Option.None }
          ; _
          }
        , _ ) ->
        (* [identifier] is known to be a free substitution variable because
           its meta de Bruijn level is unknown, so we do not signal it as an
           illegal free variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_meta_level_variable state identifier
            (Entry.make_substitution_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_substitution_variable

  let add_free_context_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc = Entry.Context_variable { meta_level = Option.None }
          ; _
          }
        , _ ) ->
        (* [identifier] is known to be a free context variable because its
           meta de Bruijn level is unknown, so we do not signal it as an
           illegal free variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_meta_level_variable state identifier
            (Entry.make_context_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_context_variable

  let add_computation_pattern_variable state ?location identifier =
    match lookup_toplevel_opt state identifier with
    | Option.Some
        ( { Entry.desc =
              Entry.Computation_variable { comp_level = Option.None }
          ; _
          }
        , _ ) ->
        (* [identifier] is known to be a free computationn variable because
           its computation de Bruijn level is unknown, so we do not signal it
           as an illegal free variable. *)
        ()
    | _ ->
        if state.free_variables_allowed then
          add_free_comp_level_variable state identifier
            (Entry.make_computation_variable_entry ?location identifier)
        else
          Error.raise_at1
            (Identifier.location identifier)
            Illegal_free_computation_variable

  let add_bound_pattern_meta_level_variable state ?location identifier
      make_entry =
    match get_current_frame state with
    | Pattern_frame frame ->
        let pattern_entry =
          make_entry ?location identifier
            ~meta_level:
              (Option.some
                 (Meta_level.of_int frame.pattern_bindings.meta_context_size))
        in
        let expression_entry =
          make_entry ?location identifier
            ~meta_level:
              (Option.some
                 (Meta_level.of_int
                    frame.expression_bindings.meta_context_size))
        in
        Binding_tree.add_toplevel identifier pattern_entry
          frame.pattern_bindings.bindings;
        increment_meta_context_size frame.pattern_bindings;
        frame.pattern_variables_rev <-
          identifier :: frame.pattern_variables_rev;
        Binding_tree.add_toplevel identifier expression_entry
          frame.expression_bindings.bindings;
        increment_meta_context_size frame.expression_bindings
    | Plain_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid plain frame, expected a pattern frame"
             __FUNCTION__)
    | Module_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid module frame, expected a pattern frame"
             __FUNCTION__)

  let add_bound_pattern_meta_variable state ?location identifier =
    add_bound_pattern_meta_level_variable state ?location identifier
      Entry.make_meta_variable_entry

  let add_bound_pattern_parameter_variable state ?location identifier =
    add_bound_pattern_meta_level_variable state ?location identifier
      Entry.make_parameter_variable_entry

  let add_bound_pattern_substitution_variable state ?location identifier =
    add_bound_pattern_meta_level_variable state ?location identifier
      Entry.make_substitution_variable_entry

  let add_bound_pattern_context_variable state ?location identifier =
    add_bound_pattern_meta_level_variable state ?location identifier
      Entry.make_context_variable_entry

  let with_bound_lf_variable state ?location identifier m =
    add_lf_variable state ?location identifier;
    let x = m state in
    remove_lf_binding state identifier;
    x

  let with_bound_meta_variable state ?location identifier m =
    add_meta_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_parameter_variable state ?location identifier m =
    add_parameter_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_substitution_variable state ?location identifier m =
    add_substitution_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_context_variable state ?location identifier m =
    add_context_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_contextual_variable state ?location identifier m =
    add_contextual_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_comp_variable state ?location identifier m =
    add_comp_variable state ?location identifier;
    let x = m state in
    remove_comp_binding state identifier;
    x

  let with_bound_pattern_meta_variable state ?location identifier m =
    add_bound_pattern_meta_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_pattern_parameter_variable state ?location identifier m =
    add_bound_pattern_parameter_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_pattern_substitution_variable state ?location identifier m =
    add_bound_pattern_substitution_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_bound_pattern_context_variable state ?location identifier m =
    add_bound_pattern_context_variable state ?location identifier;
    let x = m state in
    remove_meta_binding state identifier;
    x

  let with_shifted_lf_context state m =
    shift_lf_context state;
    let x = m state in
    unshift_lf_context state;
    x

  let with_shifted_meta_context state m =
    shift_meta_context state;
    let x = m state in
    unshift_meta_context state;
    x

  let with_shifted_comp_context state m =
    shift_comp_context state;
    let x = m state in
    unshift_comp_context state;
    x

  let add_lf_type_constant state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_lf_type_constant_entry ?location identifier cid)

  let add_lf_term_constant state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_lf_term_constant_entry ?location identifier cid)

  let add_schema_constant state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_schema_constant_entry ?location identifier cid)

  let add_inductive_computation_type_constant state ?location identifier cid
      =
    add_declaration state identifier
      (Entry.make_computation_inductive_type_constant_entry ?location
         identifier cid)

  let add_stratified_computation_type_constant state ?location identifier cid
      =
    add_declaration state identifier
      (Entry.make_computation_stratified_type_constant_entry ?location
         identifier cid)

  let add_coinductive_computation_type_constant state ?location identifier
      cid =
    add_declaration state identifier
      (Entry.make_computation_coinductive_type_constant_entry ?location
         identifier cid)

  let add_abbreviation_computation_type_constant state ?location identifier
      cid =
    add_declaration state identifier
      (Entry.make_computation_abbreviation_type_constant_entry ?location
         identifier cid)

  let add_computation_term_constructor state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_computation_term_constructor_entry ?location identifier cid)

  let add_computation_term_destructor state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_computation_term_destructor_entry ?location identifier cid)

  let add_program_constant state ?location identifier cid =
    add_declaration state identifier
      (Entry.make_program_constant_entry ?location identifier cid)

  let push_new_module_frame state =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    let module_frame =
      Module_frame
        { bindings =
            { current_frame_bindings_state with
              bindings = Binding_tree.create ()
            }
        ; declarations = Binding_tree.create ()
        }
    in
    push_frame state module_frame

  let add_module state ?location identifier cid m =
    push_new_module_frame state;
    let x = m state in
    (match get_current_frame state with
    | Plain_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid plain frame, expected a module frame" __FUNCTION__)
    | Pattern_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid pattern frame, expected a module frame"
             __FUNCTION__)
    | Module_frame { declarations; _ } ->
        ignore (pop_frame state);
        add_declaration state ~subtree:declarations identifier
          (Entry.make_module_entry ?location identifier cid));
    x

  let with_frame state m =
    push_new_plain_frame state;
    let x = m state in
    ignore (pop_frame state);
    x

  let with_parent_frame state m =
    let frame = pop_frame state in
    let x = with_frame state m in
    push_frame state frame;
    x

  let with_bindings_checkpoint state m =
    let original_frames_count = List1.length state.frames in
    (* Push a fresh module frame so that [m] may add declarations *)
    push_new_module_frame state;
    Fun.protect
      ~finally:(fun () ->
        let final_frames_count = List1.length state.frames in
        if
          final_frames_count - original_frames_count
          >= 1 (* We expect there to at least be the new module frame *)
        then
          (* We have to count frames because [m] may add new frames. This is
             not foolproof because [m] could have discarded too many frames
             and added some more. *)
          Fun.repeat (final_frames_count - original_frames_count) (fun () ->
              ignore (pop_frame state))
        else
          Error.raise_violation
            (Format.asprintf
               "[%s] invalid states, there are fewer frames than there \
                originally were"
               __FUNCTION__))
      (fun () -> m state)

  let allow_free_variables state m =
    let free_variables_state = are_free_variables_allowed state in
    enable_free_variables state;
    let x = m state in
    set_free_variables_allowed_state state free_variables_state;
    x

  let disallow_free_variables state m =
    let free_variables_state = are_free_variables_allowed state in
    disable_free_variables state;
    let x = m state in
    set_free_variables_allowed_state state free_variables_state;
    x

  let with_free_variables_as_pattern_variables state ~pattern ~expression =
    let current_frame_bindings_state =
      get_current_frame_bindings_state state
    in
    let pattern_frame =
      Pattern_frame
        { pattern_bindings = create_empty_bindings ()
        ; pattern_variables_rev = []
        ; expression_bindings =
            { bindings = Binding_tree.create ()
            ; lf_context_size = current_frame_bindings_state.lf_context_size
            ; meta_context_size =
                current_frame_bindings_state.meta_context_size
            ; comp_context_size =
                current_frame_bindings_state.comp_context_size
            }
        }
    in
    push_frame state pattern_frame;
    let pattern' = allow_free_variables state (fun state -> pattern state) in
    match pop_frame state with
    | Module_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid module frame, expected a pattern frame"
             __FUNCTION__)
    | Plain_frame _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] invalid plain frame, expected a pattern frame"
             __FUNCTION__)
    | Pattern_frame { pattern_variables_rev; expression_bindings; _ } -> (
        match
          Identifier.find_duplicates (List.rev pattern_variables_rev)
        with
        | Option.Some duplicates ->
            raise_duplicate_identifiers_exception
              (fun identifiers -> Duplicate_pattern_variables identifiers)
              duplicates
        | Option.None ->
            push_frame state (Plain_frame { bindings = expression_bindings });
            let expression' = expression state pattern' in
            ignore (pop_frame state);
            expression')

  let rec add_all_mctx state cD =
    (* [cD] is a stack, so traverse it from tail to head *)
    match cD with
    | Synint.LF.Dec (cD', decl) -> (
        add_all_mctx state cD';
        match decl with
        | Synint.LF.Decl { name = u; typ = Synint.LF.CTyp _; _ } ->
            add_context_variable state (Name.to_identifier u)
        | Synint.LF.Decl
            { name = u; typ = Synint.LF.ClTyp (Synint.LF.MTyp _, _); _ } ->
            add_meta_variable state (Name.to_identifier u)
        | Synint.LF.Decl
            { name = u; typ = Synint.LF.ClTyp (Synint.LF.PTyp _, _); _ } ->
            add_parameter_variable state (Name.to_identifier u)
        | Synint.LF.Decl
            { name = u; typ = Synint.LF.ClTyp (Synint.LF.STyp _, _); _ } ->
            add_substitution_variable state (Name.to_identifier u)
        | Synint.LF.DeclOpt { name = u; _ } ->
            add_contextual_variable state (Name.to_identifier u))
    | Synint.LF.Empty -> ()

  let rec add_all_gctx state cG =
    (* [cG] is a stack, so traverse it from tail to head *)
    match cG with
    | Synint.LF.Dec (cG', Synint.Comp.CTypDecl (x, _, _))
    | Synint.LF.Dec (cG', Synint.Comp.CTypDeclOpt x) ->
        add_all_gctx state cG';
        add_comp_variable state (Name.to_identifier x)
    | Synint.LF.Empty -> ()

  let snapshot_bindings
      { bindings; lf_context_size; meta_context_size; comp_context_size } =
    let bindings' = Binding_tree.snapshot bindings in
    { bindings = bindings'
    ; lf_context_size (* Immutable *)
    ; meta_context_size (* Immutable *)
    ; comp_context_size (* Immutable *)
    }

  let snapshot_frame = function
    | Plain_frame { bindings } ->
        let bindings' = snapshot_bindings bindings in
        Plain_frame { bindings = bindings' }
    | Pattern_frame
        { pattern_bindings; pattern_variables_rev; expression_bindings } ->
        let pattern_bindings' = snapshot_bindings pattern_bindings in
        let expression_bindings' = snapshot_bindings expression_bindings in
        Pattern_frame
          { pattern_bindings = pattern_bindings'
          ; pattern_variables_rev (* Immutable *)
          ; expression_bindings = expression_bindings'
          }
    | Module_frame { bindings; declarations } ->
        let bindings' = snapshot_bindings bindings in
        let declarations' = Binding_tree.snapshot declarations in
        Module_frame { bindings = bindings'; declarations = declarations' }

  let snapshot_frames frames = List1.map snapshot_frame frames

  let snapshot_state
      { frames; free_variables_allowed; generated_fresh_variables_count } =
    let frames' = snapshot_frames frames in
    { frames = frames'
    ; free_variables_allowed (* Immutable *)
    ; generated_fresh_variables_count (* Immutable *)
    }
end
