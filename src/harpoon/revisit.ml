open Beluga
open Beluga_syntax
open Beluga_parser

[@@@warning "+A-4-44"]

(** Functor creating a visitor for rebuilding the disambiguation state, and
    take snapshots of it at each Harpoon proof. *)
module Make_disambiguation_visitor (Disambiguation_state : sig
  include Disambiguation_state.DISAMBIGUATION_STATE

  val snapshot_state : state -> state
end) =
struct
  include Disambiguation_state

  let rec revisit_sgn state snapshots sgn =
    iter_list1 state
      (fun state sgn_file -> revisit_sgn_file state snapshots sgn_file)
      sgn

  and revisit_sgn_file state snapshots sgn_file =
    let { Synint.Sgn.entries; _ } = sgn_file in
    iter_list state
      (fun state entry -> revisit_sgn_entry state snapshots entry)
      entries

  and revisit_sgn_entry state snapshots entry =
    match entry with
    | Synint.Sgn.Pragma { pragma; _ } ->
        revisit_sgn_pragma state snapshots pragma
    | Synint.Sgn.Declaration { declaration; _ } ->
        revisit_sgn_declaration state snapshots declaration
    | Synint.Sgn.Comment _ -> ()

  and revisit_sgn_pragma state _snapshots pragma =
    match pragma with
    | Synint.Sgn.NamePrag _ -> ()
    | Synint.Sgn.NotPrag _ -> ()
    | Synint.Sgn.OpenPrag { module_identifier; _ } ->
        open_module state module_identifier
    | Synint.Sgn.DefaultAssocPrag { associativity; _ } ->
        set_default_associativity state associativity
    | Synint.Sgn.PrefixFixityPrag { constant; precedence; postponed; _ } ->
        if postponed then
          add_postponed_prefix_notation state ?precedence constant
        else add_prefix_notation state ?precedence constant
    | Synint.Sgn.InfixFixityPrag
        { constant; precedence; associativity; postponed; _ } ->
        if postponed then
          add_postponed_infix_notation state ?precedence ?associativity
            constant
        else add_infix_notation state ?precedence ?associativity constant
    | Synint.Sgn.PostfixFixityPrag { constant; precedence; postponed; _ } ->
        if postponed then
          add_postponed_postfix_notation state ?precedence constant
        else add_postfix_notation state ?precedence constant
    | Synint.Sgn.AbbrevPrag { module_identifier; abbreviation; location } ->
        add_module_abbreviation state ~location module_identifier
          abbreviation
    | Synint.Sgn.Query _ -> ()

  and revisit_sgn_declaration state snapshots declaration =
    match declaration with
    | Synint.Sgn.Typ { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.Typ.explicit_arguments (Store.Cid.Typ.get cid)
        in
        add_lf_type_constant state ~location ~arity identifier
    | Synint.Sgn.Const { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.Term.explicit_arguments (Store.Cid.Term.get cid)
        in
        add_lf_term_constant state ~location ~arity identifier
    | Synint.Sgn.CompTyp
        { location
        ; cid
        ; identifier
        ; positivity_flag = Synint.Sgn.Positivity
        ; _
        } ->
        let arity =
          Store.Cid.CompTyp.explicit_arguments (Store.Cid.CompTyp.get cid)
        in
        add_inductive_computation_type_constant state ~location ~arity
          identifier
    | Synint.Sgn.CompTyp
        { location
        ; cid
        ; identifier
        ; positivity_flag = Synint.Sgn.StratifyAll _
        ; _
        } ->
        let arity =
          Store.Cid.CompTyp.explicit_arguments (Store.Cid.CompTyp.get cid)
        in
        add_stratified_computation_type_constant state ~location ~arity
          identifier
    | Synint.Sgn.CompTyp
        { location
        ; positivity_flag = Synint.Sgn.Nocheck | Synint.Sgn.Stratify _
        ; _
        } ->
        Error.raise_not_implemented ~location
          (Format.asprintf "[%s] unsupported positivity flag" __FUNCTION__)
    | Synint.Sgn.CompCotyp { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.CompCotyp.explicit_arguments
            (Store.Cid.CompCotyp.get cid)
        in
        add_coinductive_computation_type_constant state ~location ~arity
          identifier
    | Synint.Sgn.CompConst { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.CompConst.explicit_arguments
            (Store.Cid.CompConst.get cid)
        in
        add_computation_term_constructor state ~location ~arity identifier
    | Synint.Sgn.CompDest { location; identifier; _ } ->
        add_computation_term_destructor state ~location identifier
    | Synint.Sgn.CompTypAbbrev { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.CompTypDef.explicit_arguments
            (Store.Cid.CompTypDef.get cid)
        in
        add_abbreviation_computation_type_constant state ~location ~arity
          identifier
    | Synint.Sgn.Schema { location; identifier; _ } ->
        add_schema_constant state ~location identifier
    | Synint.Sgn.Val { location; cid; identifier; _ } ->
        let arity =
          Store.Cid.Comp.explicit_arguments (Store.Cid.Comp.get cid)
        in
        add_program_constant state ~location ~arity identifier
    | Synint.Sgn.Recursive_declarations { declarations; _ } ->
        revisit_recursive_sgn_declarations state snapshots declarations
    | Synint.Sgn.Module { location; identifier; entries; _ } ->
        add_module state ~location identifier (fun state ->
            iter_list state
              (fun state -> revisit_sgn_entry state snapshots)
              entries)
    | Synint.Sgn.Theorem
        { identifier; cid; body = Synint.Comp.Program _; location; _ } ->
        let arity =
          Store.Cid.Comp.explicit_arguments (Store.Cid.Comp.get cid)
        in
        add_program_constant state ~location ~arity identifier
    | Synint.Sgn.Theorem
        { identifier; cid; body = Synint.Comp.Proof _; location; _ } ->
        let arity =
          Store.Cid.Comp.explicit_arguments (Store.Cid.Comp.get cid)
        in
        add_program_constant state ~location ~arity identifier;
        Id.Prog.Hashtbl.add snapshots cid (snapshot_state state)

  and revisit_recursive_sgn_declarations state snapshots declarations =
    (* First add all the mutually recursive declarations, then take a
       snapshot of the disambiguation state, and finally associate the
       snapshot to each visited Harpoon proof. *)
    let proof_cids = ref Id.Prog.Set.empty in
    iter_list1 state
      (fun state declaration ->
        match declaration with
        | Synint.Sgn.Theorem
            { identifier; cid; body = Synint.Comp.Proof _; location; _ } ->
            (* Override the visitor for Harpoon proofs to postpone taking the
               state snapshot *)
            let arity =
              Store.Cid.Comp.explicit_arguments (Store.Cid.Comp.get cid)
            in
            add_program_constant state ~location ~arity identifier;
            proof_cids := Id.Prog.Set.add cid !proof_cids
        | _ -> revisit_sgn_declaration state snapshots declaration)
      declarations;
    let snapshot = snapshot_state state in
    Id.Prog.Set.iter
      (fun cid -> Id.Prog.Hashtbl.add snapshots cid snapshot)
      !proof_cids
end

module Disambiguation_visitor =
  Make_disambiguation_visitor (Disambiguation_state.Disambiguation_state)

let revisit_disambiguation sgn =
  let state =
    Disambiguation_state.Disambiguation_state.create_initial_state ()
  in
  let snapshots = Id.Prog.Hashtbl.create 10 in
  Disambiguation_visitor.revisit_sgn state snapshots sgn;
  let last_snapshot =
    Disambiguation_state.Disambiguation_state.snapshot_state state
  in
  (snapshots, last_snapshot)

(** Functor creating a visitor for rebuilding the indexing state, and take
    snapshots of it at each Harpoon proof. *)
module Make_indexing_visitor (Indexing_state : sig
  include Index_state.INDEXING_STATE

  val snapshot_state : state -> state
end) =
struct
  include Indexing_state

  let rec revisit_sgn state snapshots sgn =
    iter_list1 state
      (fun state sgn_file -> revisit_sgn_file state snapshots sgn_file)
      sgn

  and revisit_sgn_file state snapshots sgn_file =
    let { Synint.Sgn.entries; _ } = sgn_file in
    iter_list state
      (fun state entry -> revisit_sgn_entry state snapshots entry)
      entries

  and revisit_sgn_entry state snapshots entry =
    match entry with
    | Synint.Sgn.Pragma { pragma; _ } ->
        revisit_sgn_pragma state snapshots pragma
    | Synint.Sgn.Declaration { declaration; _ } ->
        revisit_sgn_declaration state snapshots declaration
    | Synint.Sgn.Comment _ -> ()

  and revisit_sgn_pragma state _snapshots pragma =
    match pragma with
    | Synint.Sgn.NamePrag _ -> ()
    | Synint.Sgn.NotPrag _ -> ()
    | Synint.Sgn.OpenPrag { module_identifier; _ } ->
        open_module state module_identifier
    | Synint.Sgn.DefaultAssocPrag _ -> ()
    | Synint.Sgn.PrefixFixityPrag _ -> ()
    | Synint.Sgn.InfixFixityPrag _ -> ()
    | Synint.Sgn.PostfixFixityPrag _ -> ()
    | Synint.Sgn.AbbrevPrag { module_identifier; abbreviation; location } ->
        add_module_abbreviation state ~location module_identifier
          abbreviation
    | Synint.Sgn.Query _ -> ()

  and revisit_sgn_declaration state snapshots declaration =
    match declaration with
    | Synint.Sgn.Typ { location; cid; identifier; _ } ->
        add_lf_type_constant state ~location identifier cid
    | Synint.Sgn.Const { location; cid; identifier; _ } ->
        add_lf_term_constant state ~location identifier cid
    | Synint.Sgn.CompTyp
        { location
        ; cid
        ; identifier
        ; positivity_flag = Synint.Sgn.Positivity
        ; _
        } ->
        add_inductive_computation_type_constant state ~location identifier
          cid
    | Synint.Sgn.CompTyp
        { location
        ; cid
        ; identifier
        ; positivity_flag = Synint.Sgn.StratifyAll _
        ; _
        } ->
        add_stratified_computation_type_constant state ~location identifier
          cid
    | Synint.Sgn.CompTyp
        { location
        ; positivity_flag = Synint.Sgn.Nocheck | Synint.Sgn.Stratify _
        ; _
        } ->
        Error.raise_not_implemented ~location
          (Format.asprintf "[%s] unsupported positivity flag" __FUNCTION__)
    | Synint.Sgn.CompCotyp { location; cid; identifier; _ } ->
        add_coinductive_computation_type_constant state ~location identifier
          cid
    | Synint.Sgn.CompConst { location; cid; identifier; _ } ->
        add_computation_term_constructor state ~location identifier cid
    | Synint.Sgn.CompDest { location; identifier; cid; _ } ->
        add_computation_term_destructor state ~location identifier cid
    | Synint.Sgn.CompTypAbbrev { location; cid; identifier; _ } ->
        add_abbreviation_computation_type_constant state ~location identifier
          cid
    | Synint.Sgn.Schema { location; identifier; cid; _ } ->
        add_schema_constant state ~location identifier cid
    | Synint.Sgn.Val { location; cid; identifier; _ } ->
        add_program_constant state ~location identifier cid
    | Synint.Sgn.Recursive_declarations { declarations; _ } ->
        revisit_recursive_sgn_declarations state snapshots declarations
    | Synint.Sgn.Module { location; identifier; entries; cid; _ } ->
        add_module state ~location identifier cid (fun state ->
            iter_list state
              (fun state -> revisit_sgn_entry state snapshots)
              entries)
    | Synint.Sgn.Theorem
        { identifier; cid; body = Synint.Comp.Program _; location; _ } ->
        add_program_constant state ~location identifier cid
    | Synint.Sgn.Theorem
        { identifier; cid; body = Synint.Comp.Proof _; location; _ } ->
        add_program_constant state ~location identifier cid;
        Id.Prog.Hashtbl.add snapshots cid (snapshot_state state)

  and revisit_recursive_sgn_declarations state snapshots declarations =
    (* First add all the mutually recursive declarations, then take a
       snapshot of the indexing state, and finally associate the snapshot to
       each visited Harpoon proof. *)
    let proof_cids = ref Id.Prog.Set.empty in
    iter_list1 state
      (fun state declaration ->
        match declaration with
        | Synint.Sgn.Theorem
            { identifier; cid; body = Synint.Comp.Proof _; location; _ } ->
            (* Override the visitor for Harpoon proofs to postpone taking the
               state snapshot *)
            add_program_constant state ~location identifier cid;
            proof_cids := Id.Prog.Set.add cid !proof_cids
        | _ -> revisit_sgn_declaration state snapshots declaration)
      declarations;
    let snapshot = snapshot_state state in
    Id.Prog.Set.iter
      (fun cid -> Id.Prog.Hashtbl.add snapshots cid snapshot)
      !proof_cids
end

module Indexing_visitor = Make_indexing_visitor (Index_state.Indexing_state)

let revisit_indexing sgn =
  let state = Index_state.Indexing_state.create_initial_state () in
  let snapshots = Id.Prog.Hashtbl.create 10 in
  Indexing_visitor.revisit_sgn state snapshots sgn;
  let final_snapshot = Index_state.Indexing_state.snapshot_state state in
  (snapshots, final_snapshot)
