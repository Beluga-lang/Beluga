open Support
open Beluga_syntax.Syncom

exception Unknown_constant_arity of Qualified_identifier.t

exception Unsupported_constant_for_name_generation

exception
  Invalid_prefix_arity of
    { constant : Qualified_identifier.t
    ; actual : Int.t
    }

exception
  Invalid_infix_arity of
    { constant : Qualified_identifier.t
    ; actual : Int.t
    }

exception
  Invalid_postfix_arity of
    { constant : Qualified_identifier.t
    ; actual : Int.t
    }

let () =
  Error.register_exception_printer (function
    | Unknown_constant_arity constant ->
        Format.dprintf "Can't determine the arity of constant %a."
          Qualified_identifier.pp constant
    | Unsupported_constant_for_name_generation ->
        Format.dprintf
          "Can't assign a variable name generation convention to this \
           constant."
    | Invalid_prefix_arity { constant; actual } ->
        Format.dprintf
          "Invalid prefix pragma.@ Prefix operators must have arity 1, but \
           constant %a has arity %d."
          Qualified_identifier.pp constant actual
    | Invalid_infix_arity { constant; actual } ->
        Format.dprintf
          "Invalid infix pragma.@ Infix operators must have arity 2, but \
           constant %a has arity %d."
          Qualified_identifier.pp constant actual
    | Invalid_postfix_arity { constant; actual } ->
        Format.dprintf
          "Invalid postfix pragma.@ Postfix operators must have arity 1, \
           but constant %a has arity %d."
          Qualified_identifier.pp constant actual
    | exn -> Error.raise_unsupported_exception_printing exn)

module type SIGNATURE_RECONSTRUCTION_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val get_leftover_vars :
    state -> (Abstract.free_var Synint.LF.ctx * Location.t) List.t

  val add_leftover_vars :
    state -> Abstract.free_var Synint.LF.ctx -> Location.t -> Unit.t

  val with_disabled_lf_strengthening :
    state -> location:Location.t -> (state -> 'a) -> 'a

  val with_warn_on_coverage_error :
    state -> location:Location.t -> (state -> 'a) -> 'a

  val with_coverage_checking :
    state -> location:Location.t -> (state -> 'a) -> 'a

  val set_name_generation_bases :
       state
    -> location:Location.t
    -> meta_variable_base:Identifier.t
    -> ?computation_variable_base:Identifier.t
    -> Qualified_identifier.t
    -> Unit.t

  val set_default_associativity :
    state -> ?location:Location.t -> Associativity.t -> Unit.t

  val get_default_associativity : state -> Associativity.t

  val set_default_precedence :
    state -> ?location:Location.t -> Int.t -> Unit.t

  val get_default_precedence : state -> Int.t

  val set_operator_prefix :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  val set_operator_infix :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t

  val set_operator_postfix :
       state
    -> ?location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t

  val open_module :
    state -> ?location:Location.t -> Qualified_identifier.t -> Unit.t

  val add_module_abbreviation :
       state
    -> ?location:Location.t
    -> Qualified_identifier.t
    -> abbreviation:Identifier.t
    -> Unit.t

  val with_checkpoint : state -> (state -> 'a) -> 'a

  val next_module_id : state -> Id.module_id

  val index_lf_kind : state -> Synext.lf_kind -> Synapx.LF.kind

  val index_lf_typ : state -> Synext.lf_typ -> Synapx.LF.typ

  val index_schema : state -> Synext.schema -> Synapx.LF.schema

  val index_comp_kind : state -> Synext.comp_kind -> Synapx.Comp.kind

  val index_comp_typ : state -> Synext.comp_typ -> Synapx.Comp.typ

  val index_comp_expression :
    state -> Synext.comp_expression -> Synapx.Comp.exp

  val index_comp_typedef :
       state
    -> Synext.comp_typ
    -> Synext.comp_kind
    -> Synapx.Comp.typ * Synapx.Comp.kind

  val index_comp_theorem : state -> Synext.comp_expression -> Synapx.Comp.thm

  val index_harpoon_proof : state -> Synext.harpoon_proof -> Synapx.Comp.thm

  val add_lf_type_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_typ -> Unit.t

  val add_lf_term_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_term -> Unit.t

  val add_schema_constant :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_schema -> Unit.t

  val add_prog :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val add_comp_val :
    state -> ?location:Location.t -> Identifier.t -> Id.cid_prog -> Unit.t

  val add_comp_typedef :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typdef
    -> Unit.t

  val add_comp_inductive_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_comp_stratified_type_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_typ
    -> Unit.t

  val add_comp_cotype_constant :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_cotyp
    -> Unit.t

  val add_comp_constructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_const
    -> Unit.t

  val add_comp_destructor :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.cid_comp_dest
    -> Unit.t

  val add_module :
       state
    -> ?location:Location.t
    -> Identifier.t
    -> Id.module_id
    -> (state -> 'a)
    -> 'a

  val freeze_all_unfrozen_declarations : state -> Unit.t
end

module Make_signature_reconstruction_state
    (Index_state : Index_state.INDEXING_STATE)
    (Index : Index.INDEXER with type state = Index_state.state) =
struct
  type state =
    { mutable leftover_vars :
        (Abstract.free_var Synint.LF.ctx * Location.t) List.t
          (** The list of leftover variables from the abstraction phase. *)
    ; index_state : Index_state.state
          (** The current state for replacing constants with IDs and
              variables with de Bruijn indices. *)
    ; mutable default_associativity : Associativity.t
          (** The default associativity of user-defined infix operators. *)
    ; mutable default_precedence : Int.t
          (** The default precedence of user-defined operators. *)
    ; mutable modules : Int.t
          (** The number of reconstructed modules. Used for generating module
              IDs. *)
    ; mutable unfrozen_declarations :
        [ `Typ of Id.cid_typ
        | `Comp_typ of Id.cid_comp_typ
        | `Comp_cotyp of Id.cid_comp_cotyp
        ]
        List.t
          (** The list of declarations that are not frozen, by ID.

              For instance, unfrozen LF type declarations can have
              constructors added to them. *)
    }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let create_initial_state index_state =
    { leftover_vars = []
    ; index_state
    ; default_associativity = Synext.default_associativity
    ; default_precedence = Synext.default_precedence
    ; modules = 0
    ; unfrozen_declarations = []
    }

  let clear_state ~clear_index_state state =
    state.leftover_vars <- [];
    clear_index_state state.index_state;
    state.default_associativity <- Synext.default_associativity;
    state.default_precedence <- Synext.default_precedence;
    state.modules <- 0;
    state.unfrozen_declarations <- []

  let get_leftover_vars state = state.leftover_vars

  let add_leftover_vars state vars location =
    match vars with
    | Synint.LF.Empty -> ()
    | Synint.LF.Dec _ ->
        state.leftover_vars <- (vars, location) :: state.leftover_vars

  let with_disabled_lf_strengthening state ~location:_ m =
    let initial_strengthen = !Lfrecon.strengthen in
    Lfrecon.strengthen := false;
    Fun.protect
      (fun () -> m state)
      ~finally:(fun () -> Lfrecon.strengthen := initial_strengthen)

  let with_warn_on_coverage_error state ~location:_ m =
    let initial_enableCoverage, initial_warningOnly =
      (!Coverage.enableCoverage, !Coverage.warningOnly)
    in
    Coverage.enableCoverage := true;
    Coverage.warningOnly := true;
    Fun.protect
      (fun () -> m state)
      ~finally:(fun () ->
        Coverage.enableCoverage := initial_enableCoverage;
        Coverage.warningOnly := initial_warningOnly)

  let with_coverage_checking state ~location:_ m =
    let initial_enableCoverage = !Coverage.enableCoverage in
    Coverage.enableCoverage := true;
    Fun.protect
      (fun () -> m state)
      ~finally:(fun () -> Coverage.enableCoverage := initial_enableCoverage)

  let[@inline] set_default_associativity state ?location:_
      default_associativity =
    state.default_associativity <- default_associativity

  let get_default_associativity state = state.default_associativity

  let[@inline] set_default_precedence state ?location:_ default_precedence =
    state.default_precedence <- default_precedence

  let get_default_precedence state = state.default_precedence

  let add_unfrozen_declaration state entry =
    state.unfrozen_declarations <- entry :: state.unfrozen_declarations

  let add_lf_type_constant state ?location identifier cid =
    add_unfrozen_declaration state (`Typ cid);
    Index_state.add_lf_type_constant state.index_state ?location identifier
      cid

  let add_lf_term_constant state ?location identifier cid =
    Index_state.add_lf_term_constant state.index_state ?location identifier
      cid

  let add_schema_constant state ?location identifier cid =
    Index_state.add_schema_constant state.index_state ?location identifier
      cid

  let add_prog state ?location identifier cid =
    Index_state.add_program_constant state.index_state ?location identifier
      cid

  let add_comp_val state ?location identifier cid =
    Index_state.add_program_constant state.index_state ?location identifier
      cid

  let add_comp_typedef state ?location identifier cid =
    Index_state.add_abbreviation_computation_type_constant state.index_state
      ?location identifier cid

  let add_comp_inductive_type_constant state ?location identifier cid =
    add_unfrozen_declaration state (`Comp_typ cid);
    Index_state.add_inductive_computation_type_constant state.index_state
      ?location identifier cid

  let add_comp_stratified_type_constant state ?location identifier cid =
    add_unfrozen_declaration state (`Comp_typ cid);
    Index_state.add_stratified_computation_type_constant state.index_state
      ?location identifier cid

  let add_comp_cotype_constant state ?location identifier cid =
    add_unfrozen_declaration state (`Comp_cotyp cid);
    Index_state.add_coinductive_computation_type_constant state.index_state
      ?location identifier cid

  let add_comp_constructor state ?location identifier cid =
    Index_state.add_computation_term_constructor state.index_state ?location
      identifier cid

  let add_comp_destructor state ?location identifier cid =
    Index_state.add_computation_term_destructor state.index_state ?location
      identifier cid

  let add_module state ?location identifier cid m =
    let default_associativity = get_default_associativity state in
    let default_precedence = get_default_precedence state in
    let x =
      Index_state.add_module state.index_state ?location identifier cid
        (fun _index_state -> m state)
    in
    set_default_associativity state default_associativity;
    set_default_precedence state default_precedence;
    x

  let next_module_id state =
    let modules' = state.modules + 1 in
    state.modules <- modules';
    Id.Module.of_int modules'

  (* FIXME: This implementation is incorrect. We need a deep copy of all the
     states involved in signature reconstruction. This includes states in
     term reconstruction, abstraction, type-checking and unification, which
     also includes meta-variable instantiations.

     This function should never be used by the end user. Currently, it is
     only used during the reconstruction of the signature-level [--not]
     pragma, which itself is only used in tests. This pragma should be
     deprecated in favour of a test harness that explicitely checks for
     thrown exceptions. *)
  let with_checkpoint state m = m state

  let get_default_precedence_opt state = function
    | Option.None -> get_default_precedence state
    | Option.Some precedence -> precedence

  let get_default_associativity_opt state = function
    | Option.None -> get_default_associativity state
    | Option.Some associativity -> associativity

  let lookup_operator_arity state ?location constant =
    match Index_state.index_of_constant state.index_state constant with
    | `Lf_type_constant cid ->
        Option.some Store.Cid.Typ.(explicit_arguments (get cid))
    | `Lf_term_constant cid ->
        Option.some Store.Cid.Term.(explicit_arguments (get cid))
    | `Computation_inductive_type_constant cid ->
        Option.some Store.Cid.CompTyp.(explicit_arguments (get cid))
    | `Computation_stratified_type_constant cid ->
        Option.some Store.Cid.CompTyp.(explicit_arguments (get cid))
    | `Computation_abbreviation_type_constant cid ->
        Option.some Store.Cid.CompTypDef.(explicit_arguments (get cid))
    | `Computation_coinductive_type_constant cid ->
        Option.some Store.Cid.CompCotyp.(explicit_arguments (get cid))
    | `Computation_term_constructor cid ->
        Option.some Store.Cid.CompConst.(explicit_arguments (get cid))
    | `Program_constant cid ->
        Option.some Store.Cid.Comp.(explicit_arguments (get cid))
    | _ -> Option.none

  let set_operator_prefix state ?location ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    match lookup_operator_arity state ?location constant with
    | Option.None ->
        Error.raise_at1_opt location (Unknown_constant_arity constant)
    | Option.Some arity ->
        if arity <> 1 then
          Error.raise_at1_opt location
            (Invalid_prefix_arity { constant; actual = arity })
        else
          let name = Name.make_from_qualified_identifier constant in
          Store.OpPragmas.addPragma name Fixity.prefix precedence
            Associativity.right_associative

  let set_operator_infix state ?location ?precedence ?associativity constant
      =
    let precedence = get_default_precedence_opt state precedence in
    let associativity = get_default_associativity_opt state associativity in
    match lookup_operator_arity state ?location constant with
    | Option.None ->
        Error.raise_at1_opt location (Unknown_constant_arity constant)
    | Option.Some arity ->
        if arity <> 2 then
          Error.raise_at1_opt location
            (Invalid_infix_arity { constant; actual = arity })
        else
          let name = Name.make_from_qualified_identifier constant in
          Store.OpPragmas.addPragma name Fixity.infix precedence
            associativity

  let set_operator_postfix state ?location ?precedence constant =
    let precedence = get_default_precedence_opt state precedence in
    match lookup_operator_arity state ?location constant with
    | Option.None ->
        Error.raise_at1_opt location (Unknown_constant_arity constant)
    | Option.Some arity ->
        if arity <> 1 then
          Error.raise_at1_opt location
            (Invalid_postfix_arity { constant; actual = arity })
        else
          let name = Name.make_from_qualified_identifier constant in
          Store.OpPragmas.addPragma name Fixity.postfix precedence
            Associativity.left_associative

  let add_module_abbreviation state ?location module_identifier ~abbreviation
      =
    Index_state.add_module_abbreviation state.index_state ?location
      module_identifier abbreviation

  let set_name_generation_bases state ~location ~meta_variable_base
      ?computation_variable_base constant =
    match Index_state.index_of_constant state.index_state constant with
    | `Lf_type_constant cid ->
        let m_name = Identifier.name meta_variable_base in
        let m = Option.some (Gensym.MVarData.name_gensym m_name) in
        let v_name = Option.map Identifier.name computation_variable_base in
        let v = Option.map Gensym.VarData.name_gensym v_name in
        Store.Cid.Typ.set_name_convention cid m v
    | _ -> Error.raise_at1 location Unsupported_constant_for_name_generation

  let open_module state ?location module_identifier =
    Index_state.open_module state.index_state ?location module_identifier

  let index_lf_kind state kind =
    Index.index_open_lf_kind state.index_state kind

  let index_lf_typ state typ = Index.index_open_lf_typ state.index_state typ

  let index_schema state schema = Index.index_schema state.index_state schema

  let index_comp_kind state kind =
    Index.index_open_comp_kind state.index_state kind

  let index_comp_typ state typ =
    Index.index_open_comp_typ state.index_state typ

  let index_comp_expression state expression =
    Index.index_comp_expression state.index_state expression

  let index_comp_typedef state typ kind =
    Index.index_computation_typ_abbreviation state.index_state typ kind

  let index_comp_theorem state theorem =
    Index.index_comp_theorem state.index_state theorem

  let index_harpoon_proof state proof =
    Index.index_harpoon_proof state.index_state proof

  let freeze_all_unfrozen_declarations state =
    iter_list state
      (fun _state -> function
        | `Typ id -> Store.Cid.Typ.freeze id
        | `Comp_typ id -> Store.Cid.CompTyp.freeze id
        | `Comp_cotyp id -> Store.Cid.CompCotyp.freeze id)
      state.unfrozen_declarations;
    state.unfrozen_declarations <- []
end

module Signature_reconstruction_state =
  Make_signature_reconstruction_state
    (Index_state.Indexing_state)
    (Index.Indexer)
