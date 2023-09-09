open Support
open Beluga_syntax

[@@@warning "+A-4-44"]

module C = Whnf
module S = Substitution
module Unify = Unify.StdTrail
module P = Prettyint.DefaultPrinter
module R = Store.Cid.DefaultRenderer

let dprintf, dprint, _ = Debug.makeFunctions' (Debug.toFlags [ 11 ])

open Debug.Fmt

exception Dangling_not_pragma

exception Unexpected_entry_reconstruction_success

exception Unsupported_recursive_declaration

exception
  Missing_totality_declarations of
    { programs_with : Identifier.t List.t
    ; programs_without : Identifier.t List.t
    }

exception Too_many_totality_declaration_arguments of Identifier.t

exception
  Totality_declaration_program_mismatch of
    { expected_program : Identifier.t
          (** The identifier of the program the totality declaration is
              attached to *)
    ; actual_program : Identifier.t
          (** The program identifier in the totality declaration *)
    }

exception
  Unbound_totality_declaration_argument of
    { unbound_argument : Identifier.t
    ; arguments : Identifier.t Option.t List.t
    }

exception Invalid_lf_typ_target

exception Invalid_comp_typ_target

exception Invalid_comp_cotyp_target

exception
  Lf_typ_target_mismatch of
    { constant : Identifier.t
    ; expected : Identifier.t
    ; actual : Qualified_identifier.t
    }

exception
  Comp_typ_target_mismatch of
    { constant : Identifier.t
    ; expected : Identifier.t
    ; actual : Qualified_identifier.t
    }

exception
  Comp_cotyp_target_mismatch of
    { constant : Identifier.t
    ; expected : Identifier.t
    ; actual : Qualified_identifier.t
    }

exception No_positive of Identifier.t

exception No_stratify of Identifier.t

exception
  No_stratify_or_positive of String.t (* TODO: Should be an identifier *)

let () =
  Error.register_exception_printer (function
    | Dangling_not_pragma ->
        Format.dprintf
          "This `--not' pragma must precede some signature entry."
    | Unexpected_entry_reconstruction_success ->
        Format.dprintf "%a" Format.pp_print_text
          "This signature entry was successfully reconstructed, but the \
           `--not' pragma indicates that it was expected to fail \
           reconstruction."
    | Unsupported_recursive_declaration ->
        Format.dprintf "%a" Format.pp_print_text
          "Reconstruction of this declaration is unsupported in a mutually \
           recursive group of declarations."
    | Missing_totality_declarations { programs_with; programs_without } ->
        Format.dprintf
          "@[<v 0>@[%a@]@]The function(s)@,\
          \  @[<hov>%a@]@,\
           have totality declarations, but the function(s)@,\
          \  @[<hov>%a@]@,\
           are missing totality declarations." Format.pp_print_text
          "This mutual definition block does not have consistent totality \
           declarations. Either all or none of functions must be declared \
           total."
          (List.pp ~pp_sep:Format.comma Identifier.pp)
          programs_with
          (List.pp ~pp_sep:Format.comma Identifier.pp)
          programs_without
    | Too_many_totality_declaration_arguments program ->
        Format.dprintf
          "The totality declaration for %a has too many arguments."
          Identifier.pp program
    | Totality_declaration_program_mismatch
        { expected_program; actual_program } ->
        Format.dprintf
          "@[<v 0>@[Expected totality declaration for %a.@]@,\
           @[Found totality declaration for %a.@]@]" Identifier.pp
          expected_program Identifier.pp actual_program
    | Unbound_totality_declaration_argument { unbound_argument; arguments }
      ->
        let pp_argument ppf = function
          | Option.None -> Format.pp_print_string ppf "_"
          | Option.Some argument -> Identifier.pp ppf argument
        in
        Format.dprintf
          "The argument %a does not appear in argument list @[<h>%a@]."
          Identifier.pp unbound_argument
          (List.pp ~pp_sep:Format.comma pp_argument)
          arguments
    | Invalid_lf_typ_target ->
        Format.dprintf "%a" Format.pp_print_text
          "This LF type is expected to end with the application of an LF \
           type-level constant."
    | Invalid_comp_typ_target ->
        Format.dprintf "%a" Format.pp_print_text
          "This computation-level type is expected to end with the \
           application of a computation-level type constant."
    | Invalid_comp_cotyp_target ->
        Format.dprintf "%a" Format.pp_print_text
          "This computation-level type is expected to begin with the \
           application of a computation-level cotype constant."
    | Lf_typ_target_mismatch { constant; expected; actual } ->
        Format.dprintf
          "@[<v 2>@[Wrong target data type for LF constructor %a.@]@,\
           @[Expected type %a@]@,\
           @[Actual type %a@]@]" Identifier.pp constant Identifier.pp
          expected Qualified_identifier.pp actual
    | Comp_typ_target_mismatch { constant; expected; actual } ->
        Format.dprintf
          "@[<v 2>@[Wrong target data type for computation-level \
           constructor %a.@]@,\
           @[Expected type %a@]@,\
           @[Actual type %a@]@]" Identifier.pp constant Identifier.pp
          expected Qualified_identifier.pp actual
    | Comp_cotyp_target_mismatch { constant; expected; actual } ->
        Format.dprintf
          "@[<v 2>@[Wrong target data type for computation-level destructor \
           %a.@]@,\
           @[Expected type %a@]@,\
           @[Actual type %a@]@]" Identifier.pp constant Identifier.pp
          expected Qualified_identifier.pp actual
    | No_positive identifier ->
        Format.dprintf "Positivity checking of constructor %a fails."
          Identifier.pp identifier
    | No_stratify identifier ->
        Format.dprintf "Stratification checking of constructor %a fails."
          Identifier.pp identifier
    | No_stratify_or_positive identifier ->
        Format.dprintf
          "Stratification or positivity checking of datatype %a fails."
          String.pp identifier
    | exn -> Error.raise_unsupported_exception_printing exn)

let fmt_ppr_leftover_vars ppf =
  Format.fprintf ppf "@[<v>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut
       (fun ppf (cQ, location) ->
         Format.fprintf ppf "@[<2>@[%a@] |-@ @[%a@]@]"
           Abstract.fmt_ppr_collection cQ Location.pp location))

let ppr_leftover_vars = fmt_ppr_leftover_vars Format.std_formatter

module type SIGNATURE_RECONSTRUCTION = sig
  include Imperative_state.IMPERATIVE_STATE

  val reconstruct_signature : state -> Synext.signature -> Synint.Sgn.sgn

  val reconstruct_signature_file :
    state -> Synext.signature_file -> Synint.Sgn.sgn_file
end

module Make
    (Signature_reconstruction_state : Recsgn_state
                                      .SIGNATURE_RECONSTRUCTION_STATE) :
  SIGNATURE_RECONSTRUCTION
    with type state = Signature_reconstruction_state.state = struct
  include Signature_reconstruction_state

  let rec get_lf_typ_target = function
    | Synext.LF.Typ.Constant { identifier; _ } -> identifier
    | Synext.LF.Typ.Arrow { range; _ } -> get_lf_typ_target range
    | Synext.LF.Typ.Pi { body; _ } -> get_lf_typ_target body
    | Synext.LF.Typ.Application { applicand; _ } ->
        let rec get_lf_typ_target = function
          | Synext.LF.Typ.Constant { identifier; _ } -> identifier
          | Synext.LF.Typ.Application { applicand; _ } ->
              get_lf_typ_target applicand
          | (Synext.LF.Typ.Arrow _ | Synext.LF.Typ.Pi _) as typ ->
              let location = Synext.location_of_lf_typ typ in
              Error.raise_at1 location Invalid_lf_typ_target
        in
        get_lf_typ_target applicand

  let rec get_comp_typ_target = function
    | Synext.Comp.Typ.Inductive_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Stratified_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Coinductive_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
        identifier
    | Synext.Comp.Typ.Pi { body; _ } -> get_comp_typ_target body
    | Synext.Comp.Typ.Arrow { range; _ } -> get_comp_typ_target range
    | (Synext.Comp.Typ.Cross _ | Synext.Comp.Typ.Box _) as typ ->
        let location = Synext.location_of_comp_typ typ in
        Error.raise_at1 location Invalid_comp_typ_target
    | Synext.Comp.Typ.Application { applicand; _ } ->
        let rec get_comp_typ_target = function
          | Synext.Comp.Typ.Inductive_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Stratified_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Coinductive_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
              identifier
          | Synext.Comp.Typ.Application { applicand; _ } ->
              get_comp_typ_target applicand
          | ( Synext.Comp.Typ.Pi _ | Synext.Comp.Typ.Arrow _
            | Synext.Comp.Typ.Cross _ | Synext.Comp.Typ.Box _ ) as typ ->
              let location = Synext.location_of_comp_typ typ in
              Error.raise_at1 location Invalid_comp_typ_target
        in
        get_comp_typ_target applicand

  let get_comp_cotyp_target = function
    | Synext.Comp.Typ.Inductive_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Stratified_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Coinductive_typ_constant { identifier; _ }
    | Synext.Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
        identifier
    | ( Synext.Comp.Typ.Pi _ | Synext.Comp.Typ.Arrow _
      | Synext.Comp.Typ.Cross _ | Synext.Comp.Typ.Box _ ) as typ ->
        let location = Synext.location_of_comp_typ typ in
        Error.raise_at1 location Invalid_comp_cotyp_target
    | Synext.Comp.Typ.Application { applicand; _ } ->
        let rec get_comp_cotyp_target = function
          | Synext.Comp.Typ.Inductive_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Stratified_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Coinductive_typ_constant { identifier; _ }
          | Synext.Comp.Typ.Abbreviation_typ_constant { identifier; _ } ->
              identifier
          | Synext.Comp.Typ.Application { applicand; _ } ->
              get_comp_cotyp_target applicand
          | ( Synext.Comp.Typ.Pi _ | Synext.Comp.Typ.Arrow _
            | Synext.Comp.Typ.Cross _ | Synext.Comp.Typ.Box _ ) as typ ->
              let location = Synext.location_of_comp_typ typ in
              Error.raise_at1 location Invalid_comp_cotyp_target
        in
        get_comp_cotyp_target applicand

  let rec get_target_cid_comptyp = function
    | Synint.Comp.TypBase (_, a, _) -> a
    | Synint.Comp.TypArr (_, _, tau) -> get_target_cid_comptyp tau
    | Synint.Comp.TypPiBox (_, _, tau) -> get_target_cid_comptyp tau
    | ( Synint.Comp.TypCobase _ | Synint.Comp.TypDef _ | Synint.Comp.TypBox _
      | Synint.Comp.TypCross _ | Synint.Comp.TypClo _ | Synint.Comp.TypInd _
        ) as tau ->
        let location = Synint.Comp.loc_of_typ tau in
        Error.raise_at1 location Invalid_comp_typ_target

  let get_target_cid_compcotyp = function
    | Synint.Comp.TypCobase (_, a, _) -> a
    | ( Synint.Comp.TypArr _ | Synint.Comp.TypPiBox _ | Synint.Comp.TypBase _
      | Synint.Comp.TypDef _ | Synint.Comp.TypBox _ | Synint.Comp.TypCross _
      | Synint.Comp.TypClo _ | Synint.Comp.TypInd _ ) as tau ->
        let location = Synint.Comp.loc_of_typ tau in
        Error.raise_at1 location Invalid_comp_cotyp_target

  let rec reconstruct_signature state signature_files =
    traverse_list1 state reconstruct_signature_file signature_files

  and reconstruct_signature_file state file =
    let { Synext.Signature.global_pragmas; entries; location } = file in
    let global_pragmas', entries' =
      with_applied_global_pragmas state global_pragmas
        (fun state global_pragmas' ->
          let entries' = reconstruct_signature_entries state entries in
          (global_pragmas', entries'))
    in
    freeze_all_unfrozen_declarations state;
    { Synint.Sgn.global_pragmas = global_pragmas'
    ; entries = entries'
    ; location
    }

  and with_applied_global_pragmas state global_pragmas f =
    match global_pragmas with
    | [] -> f state []
    | x :: xs ->
        with_applied_global_pragma state x (fun state y ->
            with_applied_global_pragmas state xs (fun state ys ->
                f state (y :: ys)))

  and with_applied_global_pragma state global_pragma f =
    match global_pragma with
    | Synext.Signature.Global_pragma.No_strengthening { location } ->
        let global_pragma' = Synint.Sgn.No_strengthening { location } in
        with_disabled_lf_strengthening state ~location (fun state ->
            f state global_pragma')
    | Synext.Signature.Global_pragma.Warn_on_coverage_error { location } ->
        let global_pragma' =
          Synint.Sgn.Warn_on_coverage_error { location }
        in
        with_warn_on_coverage_error state ~location (fun state ->
            f state global_pragma')
    | Synext.Signature.Global_pragma.Initiate_coverage_checking { location }
      ->
        let global_pragma' =
          Synint.Sgn.Initiate_coverage_checking { location }
        in
        with_coverage_checking state ~location (fun state ->
            f state global_pragma')

  (** [get_constant_declaration_identifier_if_can_have_fixity_pragma declaration]
      is [Option.Some identifier] if [declaration] can have a fixity pragma
      attached to it. In that case, a fixity pragma could be declared before
      it, and it would apply to [declaration]. Such a pragma is called a
      postponed fixity pragma. *)
  and get_constant_declaration_identifier_if_can_have_fixity_pragma =
    function
    | Synext.Signature.Declaration.Typ { identifier; _ }
    | Synext.Signature.Declaration.Const { identifier; _ }
    | Synext.Signature.Declaration.CompTyp { identifier; _ }
    | Synext.Signature.Declaration.CompCotyp { identifier; _ }
    | Synext.Signature.Declaration.CompConst { identifier; _ }
    | Synext.Signature.Declaration.CompTypAbbrev { identifier; _ }
    | Synext.Signature.Declaration.Theorem { identifier; _ }
    | Synext.Signature.Declaration.Proof { identifier; _ }
    | Synext.Signature.Declaration.Val { identifier; _ } ->
        Option.some identifier
    | Synext.Signature.Declaration.CompDest _
    | Synext.Signature.Declaration.Schema _
    | Synext.Signature.Declaration.Recursive_declarations _
    | Synext.Signature.Declaration.Module _ ->
        Option.none

  (** [fixable_constant_declaration_identifiers entry] is the set of
      identifiers in [entry] to which a postponed fixity pragma can be
      attached. [entry] is assumed to be the signature-level entry that
      immediately follows a set of fixity pragmas. *)
  and fixable_constant_declaration_identifiers = function
    | Synext.Signature.Entry.Declaration
        { declaration =
            Synext.Signature.Declaration.Recursive_declarations
              { declarations; _ }
        ; _
        } ->
        (* Collect all the declaration identifiers in the group of mutually
           recursive declarations that can have fixity pragmas attached to
           them *)
        List.fold_left
          (fun identifier_set declaration ->
            match
              get_constant_declaration_identifier_if_can_have_fixity_pragma
                declaration
            with
            | Option.None -> identifier_set
            | Option.Some identifier ->
                Identifier.Set.add identifier identifier_set)
          Identifier.Set.empty
          (List1.to_list declarations)
    | Synext.Signature.Entry.Declaration { declaration; _ } -> (
        (* Return the declaration identifier if it can have a fixity pragma
           attached to it *)
        match
          get_constant_declaration_identifier_if_can_have_fixity_pragma
            declaration
        with
        | Option.None -> Identifier.Set.empty
        | Option.Some identifier -> Identifier.Set.singleton identifier)
    | _ -> Identifier.Set.empty

  (** [is_entry_fixity_pragma_or_comment entry] is [true] if and only if
      [entry] is a fixity pragma or a documentation comment.

      This predicate is used to determine which signature entries can be
      skipped over when looking ahead to find which signature-level
      declaration can a postponed fixity pragma be applied to. *)
  and is_entry_fixity_pragma_or_comment = function
    | Synext.Signature.Entry.Pragma
        { pragma =
            ( Synext.Signature.Pragma.Prefix_fixity _
            | Synext.Signature.Pragma.Infix_fixity _
            | Synext.Signature.Pragma.Postfix_fixity _ )
        ; _
        }
    | Synext.Signature.Entry.Comment _ ->
        true
    | _ -> false

  (** [reconstruct_postponable_fixity_pragma state applicable_constant_identifiers entry]
      pretty-prints the fixity pragma or documentation comment [entry] with
      respect to the pretty-printing state [state] and the set
      [applicable_constant_identifiers] of identifiers in the signature-level
      declaration that follows the pragma/comment.

      If [entry] is a pragma whose constant is in
      [applicable_constant_identifiers], then [entry] is a postponed fixity
      pragma, and its application should wait until the later declaration is
      in scope.

      It is assumed that [entry] does not affect the lookahead for the target
      declaration for a postponed fixity pragma. That is, [entry] must be a
      prefix, infix or postfix fixity pragma, or a documentation comment. *)
  and reconstruct_postponable_fixity_pragma state
      applicable_constant_identifiers =
    let is_constant_a_plain_identifier constant =
      List.null (Qualified_identifier.namespaces constant)
    in
    let is_fixity_constant_postponed constant =
      is_constant_a_plain_identifier constant
      && Identifier.Set.mem
           (Qualified_identifier.name constant)
           applicable_constant_identifiers
    in
    function
    | Synext.Signature.Entry.Comment _ as entry ->
        reconstruct_signature_entry state entry
    | Synext.Signature.Entry.Pragma
        { pragma =
            Synext.Signature.Pragma.Prefix_fixity
              { constant; precedence; location }
        ; location = entry_location
        } ->
        let add_notation =
          if is_fixity_constant_postponed constant then
            add_postponed_prefix_notation
          else add_prefix_notation
        in
        add_notation state ?precedence constant;
        Synint.Sgn.Pragma
          { pragma =
              Synint.Sgn.PrefixFixityPrag { location; constant; precedence }
          ; location = entry_location
          }
    | Synext.Signature.Entry.Pragma
        { pragma =
            Synext.Signature.Pragma.Infix_fixity
              { constant; precedence; associativity; location }
        ; location = entry_location
        } ->
        let add_notation =
          if is_fixity_constant_postponed constant then
            add_postponed_infix_notation
          else add_infix_notation
        in
        add_notation state ?precedence ?associativity constant;
        Synint.Sgn.Pragma
          { pragma =
              Synint.Sgn.InfixFixityPrag
                { location; constant; precedence; associativity }
          ; location = entry_location
          }
    | Synext.Signature.Entry.Pragma
        { pragma =
            Synext.Signature.Pragma.Postfix_fixity
              { constant; precedence; location }
        ; location = entry_location
        } ->
        let add_notation =
          if is_fixity_constant_postponed constant then
            add_postponed_postfix_notation
          else add_postfix_notation
        in
        add_notation state ?precedence constant;
        Synint.Sgn.Pragma
          { pragma =
              Synint.Sgn.PostfixFixityPrag { location; constant; precedence }
          ; location = entry_location
          }
    | _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] unexpectedly encountered an entry that is neither a \
              fixity pragma nor a documentation comment"
             __FUNCTION__)

  (** [reconstruct_signature_entries entries] reconstructs a list of
      signature entries. This in particular handles the reconstruction of
      entries that are not handled independently from one another, such as
      [--not] pragmas. *)
  and reconstruct_signature_entries state entries =
    match entries with
    | Synext.Signature.Entry.Pragma
        { location = pragma_location
        ; pragma = Synext.Signature.Pragma.Not _
        }
      :: entries -> (
        match entries with
        | [] -> Error.raise_at1 pragma_location Dangling_not_pragma
        | entry :: entries -> (
            (* The [--not] pragma indicates that we expect [entry] to fail
               reconstruction. So, we perform reconstruction of [entry]
               without keeping track of its side effects. *)
            let entry_res' =
              try
                with_checkpoint state (fun state ->
                    Result.ok (reconstruct_signature_entry state entry))
              with
              | reconstruction_error ->
                  (* The [--not] pragma was used properly *)
                  Result.error reconstruction_error
            in
            match entry_res' with
            | Result.Ok _ ->
                Error.raise_at2 pragma_location
                  (Synext.location_of_signature_entry entry)
                  Unexpected_entry_reconstruction_success
            | Result.Error _ ->
                Chatter.print 1 (fun ppf ->
                    Format.fprintf ppf
                      "Reconstruction fails for --not'd declaration@\n");
                reconstruct_signature_entries state entries))
    | Synext.Signature.Entry.Pragma
        { pragma =
            ( Synext.Signature.Pragma.Prefix_fixity _
            | Synext.Signature.Pragma.Infix_fixity _
            | Synext.Signature.Pragma.Postfix_fixity _ )
        ; _
        }
      :: _ as entries -> (
        (* Special case of pretty-printing where the fixity pragma may apply
           to a constant declared subsequently after the pragma *)
        match List.take_while is_entry_fixity_pragma_or_comment entries with
        | _, [] -> reconstruct_signature_entries state entries
        | pragmas_and_comments, entry :: entries ->
            let applicable_constant_identifiers =
              fixable_constant_declaration_identifiers entry
            in
            (* The fixity pragmas in [pragmas_and_comments] whose identifiers
               are in [applicable_constant_identifiers] are postponed fixity
               pragmas *)
            let pragmas_and_comments' =
              traverse_list state
                (fun state ->
                  reconstruct_postponable_fixity_pragma state
                    applicable_constant_identifiers)
                pragmas_and_comments
            in
            let entries' =
              reconstruct_signature_entries state (entry :: entries)
            in
            pragmas_and_comments' @ entries')
    | entry :: entries ->
        let entry' = reconstruct_signature_entry state entry in
        let entries' = reconstruct_signature_entries state entries in
        entry' :: entries'
    | [] -> []

  (** [reconstruct_signature_entry entry] reconstructs a single signature
      entry. *)
  and reconstruct_signature_entry state entry =
    match entry with
    | Synext.Signature.Entry.Comment { location; content } ->
        Synint.Sgn.Comment { location; content }
    | Synext.Signature.Entry.Pragma { pragma; location } ->
        let pragma' = reconstruct_signature_pragma state pragma in
        Synint.Sgn.Pragma { pragma = pragma'; location }
    | Synext.Signature.Entry.Declaration { declaration; location } ->
        let declaration' =
          reconstruct_signature_declaration state declaration
        in
        Synint.Sgn.Declaration { declaration = declaration'; location }

  and reconstruct_signature_pragma state pragma =
    match pragma with
    | Synext.Signature.Pragma.Not _ ->
        Error.raise_violation
          (Format.asprintf
             "[%s] --not pragma must be reconstructed with \
              [reconstruct_signature_entries]"
             __FUNCTION__)
    | Synext.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }
      ->
        (* FIXME(Marc-Antoine): Name generation conventions should not be in
           the store. They should only be recorded in a pretty-printer
           state. *)
        set_name_generation_bases state ~location ~meta_variable_base
          ?computation_variable_base constant;
        Synint.Sgn.NamePrag
          { location
          ; constant
          ; meta_variable_base
          ; computation_variable_base
          }
    | Synext.Signature.Pragma.Default_associativity
        { associativity; location } ->
        set_default_associativity state ~location associativity;
        Synint.Sgn.DefaultAssocPrag { associativity; location }
    | Synext.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        add_prefix_notation state ~location ?precedence constant;
        Synint.Sgn.PrefixFixityPrag { location; constant; precedence }
    | Synext.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        add_infix_notation state ~location ?precedence ?associativity
          constant;
        Synint.Sgn.InfixFixityPrag
          { location; constant; precedence; associativity }
    | Synext.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        add_postfix_notation state ~location ?precedence constant;
        Synint.Sgn.PostfixFixityPrag { location; constant; precedence }
    | Synext.Signature.Pragma.Open_module { location; module_identifier } ->
        freeze_all_unfrozen_declarations state;
        open_module state ~location module_identifier;
        Synint.Sgn.OpenPrag { location; module_identifier }
    | Synext.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        add_module_abbreviation state ~location module_identifier
          ~abbreviation;
        Synint.Sgn.AbbrevPrag { location; module_identifier; abbreviation }
    | Synext.Signature.Pragma.Query
        { location; identifier; typ; expected_solutions; maximum_tries } ->
        freeze_all_unfrozen_declarations state;
        reconstruct_query_pragma state location identifier typ
          expected_solutions maximum_tries

  and reconstruct_signature_declaration state declaration =
    match declaration with
    | Synext.Signature.Declaration.CompTyp { location; _ }
    | Synext.Signature.Declaration.CompCotyp { location; _ }
    | Synext.Signature.Declaration.CompConst { location; _ }
    | Synext.Signature.Declaration.CompDest { location; _ }
    | Synext.Signature.Declaration.Theorem { location; _ }
    | Synext.Signature.Declaration.Proof { location; _ } ->
        Error.raise_violation ~location
          (Format.asprintf
             "[%s] this kind of signature declaration is only supported \
              within a mutually recursive group of declarations."
             __FUNCTION__)
    | Synext.Signature.Declaration.Typ { location; identifier; kind } ->
        reconstruct_lf_typ_declaration state location identifier kind
    | Synext.Signature.Declaration.Const { location; identifier; typ } ->
        reconstruct_lf_const_declaration state location identifier typ
    | Synext.Signature.Declaration.Schema { location; identifier; schema } ->
        freeze_all_unfrozen_declarations state;
        reconstruct_schema_declaration state location identifier schema
    | Synext.Signature.Declaration.CompTypAbbrev
        { location; identifier; kind; typ } ->
        freeze_all_unfrozen_declarations state;
        reconstruct_comp_typ_abbrev_declaration state location identifier
          kind typ
    | Synext.Signature.Declaration.Val
        { location; identifier; typ; expression } ->
        freeze_all_unfrozen_declarations state;
        reconstruct_val_declaration state location identifier typ expression
    | Synext.Signature.Declaration.Recursive_declarations
        { location; declarations } ->
        freeze_all_unfrozen_declarations state;
        let declaration' =
          reconstruct_recursive_declarations state location declarations
        in
        freeze_all_unfrozen_declarations state;
        declaration'
    | Synext.Signature.Declaration.Module { location; identifier; entries }
      ->
        freeze_all_unfrozen_declarations
          state (* Can't extend definitions in a new module *);
        let module_declaration =
          reconstruct_module_declaration state location identifier entries
        in
        freeze_all_unfrozen_declarations
          state (* Can't extend definitions in the new module from outside *);
        module_declaration

  and reconstruct_lf_typ_declaration state location identifier extK =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Typ at: %a" Location.print_short location);
    dprintf (fun p ->
        p.fmt "\nIndexing type constant %a" Identifier.pp identifier);
    let apxK = index_lf_kind state extK in
    dprintf (fun p ->
        p.fmt "\nElaborating type constant %a" Identifier.pp identifier);
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    Store.FVar.clear ();
    let tK =
      Monitor.timer
        ( Monitor.type_elaboration
        , fun () ->
            let tK = Reconstruct.kind apxK in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tK )
    in
    Unify.forceGlobalCnstr ();
    let tK', i =
      Monitor.timer (Monitor.type_abstraction, fun () -> Abstract.kind tK)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt "%a : %a@\n" Identifier.pp identifier
          (P.fmt_ppr_lf_kind Synint.LF.Null P.l0)
          tK');
    Monitor.timer
      ( Monitor.type_check
      , fun () -> Check.LF.checkKind Synint.LF.Empty Synint.LF.Null tK' );
    dprintf (fun p ->
        p.fmt "DOUBLE CHECK for type constant %a successful!" Identifier.pp
          identifier);
    Typeinfo.Sgn.add location
      (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Kind tK'))
      "";
    let cid =
      Store.Cid.Typ.add (fun _cid -> Store.Cid.Typ.mk_entry name tK' i)
    in
    add_lf_type_constant state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.Typ { location; identifier; cid; kind = tK' }

  and reconstruct_lf_const_declaration state location identifier extT =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Const %a at: %a" Identifier.pp identifier
          Location.print_short location);
    let apxT = index_lf_typ state extT in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let rec get_type_family = function
      | Synapx.LF.Atom (_loc, a, _spine) -> a
      | Synapx.LF.PiTyp ((_, _, _), t) -> get_type_family t
      | Synapx.LF.Sigma _ ->
          Error.raise_violation ~location
            (Format.asprintf "[%s] unsupported sigma type" __FUNCTION__)
    in
    let constructedType = get_type_family apxT in
    dprintf (fun p ->
        p.fmt "Reconstructing term constant %a" Identifier.pp identifier);
    Store.FVar.clear ();
    let tA =
      Monitor.timer
        ( Monitor.constant_elaboration
        , fun () ->
            let tA = Reconstruct.typ Lfrecon.Pi apxT in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tA )
    in
    let cD = Synint.LF.Empty in
    dprintf (fun p ->
        p.fmt "[recSgnDecl] [Const] %a : %a" Identifier.pp identifier
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA);
    Unify.forceGlobalCnstr ();
    let tA', i =
      Monitor.timer (Monitor.constant_abstraction, fun () -> Abstract.typ tA)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt
          "[recSgnDecl] [Const] Reconstruction (with abstraction) of \
           constant: %a : %a"
          Identifier.pp identifier
          (P.fmt_ppr_lf_typ cD Synint.LF.Null P.l0)
          tA');
    Monitor.timer
      ( Monitor.constant_check
      , fun () ->
          Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', S.LF.id) );
    Typeinfo.Sgn.add location
      (Typeinfo.Sgn.mk_entry (Typeinfo.Sgn.Typ tA'))
      "";
    let cid =
      Store.Cid.Term.add' location constructedType (fun _cid ->
          Store.Cid.Term.mk_entry name tA' i)
    in
    add_lf_term_constant state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.Const { location; identifier; cid; typ = tA' }

  and reconstruct_comp_typ_constant state location identifier kind
      datatype_flavour =
    dprintf (fun p ->
        p.fmt "Indexing computation-level data-type constant %a"
          Identifier.pp identifier);
    let apx_kind = index_comp_kind state kind in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    Store.FVar.clear ();
    dprintf (fun p ->
        p.fmt "Elaborating data-type declaration %a" Identifier.pp identifier);
    let cK =
      Monitor.timer
        ( Monitor.ctype_elaboration
        , fun () ->
            let cK = Reconstruct.compkind apx_kind in
            Reconstruct.solve_fvarCnstr Lfrecon.Pibox;
            cK )
    in
    Unify.forceGlobalCnstr ();
    let cK', i =
      Monitor.timer
        (Monitor.ctype_abstraction, fun () -> Abstract.compkind cK)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt "%a : %a@\n" Identifier.pp identifier
          (P.fmt_ppr_cmp_kind Synint.LF.Empty P.l0)
          cK');
    Monitor.timer
      ( Monitor.ctype_check
      , fun () -> Check.Comp.checkKind Synint.LF.Empty cK' );
    dprintf (fun p ->
        p.fmt "DOUBLE CHECK for data type constant %a successful!"
          Identifier.pp identifier);

    let p =
      match datatype_flavour with
      | `Stratified -> Synint.Sgn.StratifyAll location
      | `Inductive -> Synint.Sgn.Positivity
    in
    let name = Name.make_from_identifier identifier in
    let cid =
      Store.Cid.CompTyp.add (fun _cid ->
          Store.Cid.CompTyp.mk_entry name cK' i p)
    in
    (match datatype_flavour with
    | `Stratified ->
        add_comp_stratified_type_constant state ~location identifier cid
    | `Inductive ->
        add_comp_inductive_type_constant state ~location identifier cid);
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.CompTyp
      { location; identifier; cid; kind = cK'; positivity_flag = p }

  and reconstruct_comp_cotyp_constant state location identifier kind =
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] CompCotyp at %a: %a" Identifier.pp
          identifier Location.print location);
    dprintf (fun p ->
        p.fmt "Indexing computation-level codata-type constant %a"
          Identifier.pp identifier);
    let apxK = index_comp_kind state kind in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    Store.FVar.clear ();
    dprintf (fun p ->
        p.fmt "Elaborating codata-type declaration %a" Identifier.pp
          identifier);
    let cK =
      Monitor.timer
        ( Monitor.ctype_elaboration
        , fun () ->
            let cK = Reconstruct.compkind apxK in
            Reconstruct.solve_fvarCnstr Lfrecon.Pibox;
            cK )
    in
    Unify.forceGlobalCnstr ();
    let cK', i =
      Monitor.timer
        (Monitor.ctype_abstraction, fun () -> Abstract.compkind cK)
    in

    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt "%a : %a" Identifier.pp identifier
          (P.fmt_ppr_cmp_kind Synint.LF.Empty P.l0)
          cK');
    Monitor.timer
      ( Monitor.ctype_check
      , fun () -> Check.Comp.checkKind Synint.LF.Empty cK' );
    dprintf (fun p ->
        p.fmt "DOUBLE CHECK for codata type constant %a successful!"
          Identifier.pp identifier);

    let name = Name.make_from_identifier identifier in
    let cid =
      Store.Cid.CompCotyp.add (fun _cid ->
          Store.Cid.CompCotyp.mk_entry name cK' i)
    in
    add_comp_cotype_constant state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.CompCotyp { location; identifier; cid; kind = cK' }

  and reconstruct_comp_constructor state location ~stratNum identifier typ =
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] CompConst at %a: %a" Identifier.pp
          identifier Location.print_short location);
    dprintf (fun p ->
        p.fmt "Indexing computation-level data-type constructor %a"
          Identifier.pp identifier);
    let apx_tau = index_comp_typ state typ in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let cD = Synint.LF.Empty in
    dprintf (fun p ->
        p.fmt "Elaborating data-type constructor %a" Identifier.pp identifier);
    let tau' =
      Monitor.timer
        ( Monitor.datatype_constant_type_elaboration
        , fun () -> Reconstruct.comptyp apx_tau )
    in
    Unify.forceGlobalCnstr ();
    dprint (fun () -> "Abstracting over computation-level type");
    let tau', i =
      Monitor.timer
        ( Monitor.datatype_constant_type_abstraction
        , fun () -> Abstract.comptyp tau' )
    in
    dprint (fun () -> "Abstracting over computation-level type: done");
    dprintf (fun p ->
        p.fmt
          "[recsgn] @[<v>@[<hov>@[%a@] :@ @[%a@]@]@,\
           with %d implicit parameters@]" Identifier.pp identifier
          (P.fmt_ppr_cmp_typ cD P.l0)
          tau' i);
    Monitor.timer
      ( Monitor.datatype_constant_type_check
      , fun () -> Check.Comp.checkTyp cD tau' );
    let cid_ctypfamily = get_target_cid_comptyp tau' in

    let flag = Store.Cid.CompTyp.((get cid_ctypfamily).Entry.positivity) in

    (match flag with
    | Synint.Sgn.Nocheck -> ()
    | Synint.Sgn.Positivity ->
        (* The constructor being reconstructed is that of an inductive
           datatype. *)
        if Total.positive cid_ctypfamily tau' then ()
        else Error.raise_at1 location (No_positive identifier)
    | Synint.Sgn.Stratify (loc_s, n) ->
        if Total.stratify cid_ctypfamily tau' n then ()
        else Error.raise_at1 loc_s (No_stratify identifier)
    | Synint.Sgn.StratifyAll loc_s ->
        (* The constructor being reconstructed is that of a stratified
           datatype. *)
        let t = Total.stratifyAll cid_ctypfamily tau' in
        let t' = t land !stratNum in
        if t' <> 0 then stratNum := t'
        else
          Error.raise_at1 loc_s
            (No_stratify_or_positive (R.render_cid_comp_typ cid_ctypfamily)));

    let name = Name.make_from_identifier identifier in
    let cid =
      Store.Cid.CompConst.add cid_ctypfamily (fun _ ->
          Store.Cid.CompConst.mk_entry name tau' i)
    in
    add_comp_constructor state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.CompConst { location; identifier; cid; typ = tau' }

  and reconstruct_comp_destructor state location identifier observation_type
      return_type =
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] CompDest at: %a" Location.print_short
          location);
    dprintf (fun p ->
        p.fmt "Indexing computation-level codata-type destructor %a"
          Identifier.pp identifier);
    let cD = Synint.LF.Empty in
    let apx_observation_type = index_comp_typ state observation_type in
    let apx_return_type = index_comp_typ state return_type in
    dprintf (fun p ->
        p.fmt "Elaborating codata-type destructor %a" Identifier.pp
          identifier);
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let observation_type' =
      Monitor.timer
        ( Monitor.codatatype_constant_type_elaboration
        , fun () -> Reconstruct.comptyp_cD cD apx_observation_type )
    in
    let return_type' =
      Monitor.timer
        ( Monitor.codatatype_constant_type_elaboration
        , fun () -> Reconstruct.comptyp_cD cD apx_return_type )
    in
    Unify.forceGlobalCnstr ();
    dprint (fun () -> "Abstracting over computation-level type");
    let mctx', observation_type', return_type', i =
      Monitor.timer
        ( Monitor.codatatype_constant_type_abstraction
        , fun () -> Abstract.codatatyp cD observation_type' return_type' )
    in
    dprintf (fun p ->
        p.fmt "[recSgnDecl] [CompDest] @[<v>cD1 = @[%a@]@,tau1' = @[%a@]@]"
          (P.fmt_ppr_lf_mctx P.l0) mctx'
          (P.fmt_ppr_cmp_typ mctx' P.l0)
          return_type');
    dprint (fun () -> "Abstracting over computation-level type: done");
    dprintf (fun p ->
        p.fmt "%a : %a :: %a" Identifier.pp identifier
          (P.fmt_ppr_cmp_typ mctx' P.l0)
          observation_type'
          (P.fmt_ppr_cmp_typ mctx' P.l0)
          return_type');
    Monitor.timer
      ( Monitor.codatatype_constant_type_check
      , fun () -> Check.Comp.checkTyp mctx' observation_type' );
    Monitor.timer
      ( Monitor.codatatype_constant_type_check
      , fun () -> Check.Comp.checkTyp mctx' return_type' );
    let cid_ctypfamily = get_target_cid_compcotyp observation_type' in
    let name = Name.make_from_identifier identifier in
    let cid =
      Store.Cid.CompDest.add cid_ctypfamily (fun _ ->
          Store.Cid.CompDest.mk_entry name mctx' observation_type'
            return_type' i)
    in
    add_comp_destructor state ~location identifier cid;
    Synint.Sgn.CompDest
      { location
      ; identifier
      ; cid
      ; mctx = mctx'
      ; observation_typ = observation_type'
      ; return_typ = return_type'
      }

  and reconstruct_schema_declaration state location identifier schema =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Schema at: %a@\n" Location.print_short
          location);
    let apx_schema = index_schema state schema in
    dprintf (fun p ->
        p.fmt "Reconstructing schema %a@\n" Identifier.pp identifier);
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    Store.FVar.clear ();
    let sW = Reconstruct.schema apx_schema in
    dprintf (fun p ->
        p.fmt "Elaborated schema %a : %a" Identifier.pp identifier
          (P.fmt_ppr_lf_schema P.l0)
          sW);
    Reconstruct.solve_fvarCnstr Lfrecon.Pi;
    Unify.forceGlobalCnstr ();
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    let sW' = Abstract.schema sW in
    dprintf (fun p ->
        p.fmt "Schema %a : %a after abstraction@\n" Identifier.pp identifier
          (P.fmt_ppr_lf_schema P.l0)
          sW');
    Check.LF.checkSchemaWf sW';
    dprintf (fun p ->
        p.fmt "TYPE CHECK for schema %a successful@\n" Identifier.pp
          identifier);
    let cid =
      Store.Cid.Schema.add (fun _cid -> Store.Cid.Schema.mk_entry name sW')
    in
    add_schema_constant state ~location identifier cid;
    Synint.Sgn.Schema { location; identifier; cid; schema = sW' }

  and reconstruct_comp_typ_abbrev_declaration state location identifier cK cT
      =
    let name = Name.make_from_identifier identifier in
    (* index cT in a context which contains arguments to cK *)
    let apx_tau, apxK = index_comp_typedef state cT cK in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let (cD, cT), i, cK =
      Reconstruct.comptypdef location name (apx_tau, apxK)
    in
    dprintf (fun p ->
        p.fmt "typedef %a : %a = %a" Identifier.pp identifier
          (P.fmt_ppr_cmp_kind Synint.LF.Empty P.l0)
          cK
          (P.fmt_ppr_cmp_typ cD P.l0)
          cT);
    Monitor.timer
      ( Monitor.type_abbrev_kind_check
      , fun () -> Check.Comp.checkKind Synint.LF.Empty cK );
    Monitor.timer
      (Monitor.type_abbrev_type_check, fun () -> Check.Comp.checkTyp cD cT);
    let cid =
      Store.Cid.CompTypDef.add (fun _cid ->
          Store.Cid.CompTypDef.mk_entry name i (cD, cT) cK)
    in
    add_comp_typedef state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.CompTypAbbrev
      { location; identifier; cid; kind = cK; typ = cT }

  and reconstruct_val_declaration state location identifier typ_opt
      expression =
    match typ_opt with
    | Option.None ->
        reconstruct_untyped_val_declaration state location identifier
          expression
    | Option.Some typ ->
        reconstruct_typed_val_declaration state location identifier typ
          expression

  and reconstruct_untyped_val_declaration state location identifier
      expression =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Val at: %a" Location.print_short location);
    let apx_i = index_comp_expression state expression in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let cD, cG = (Synint.LF.Empty, Synint.LF.Empty) in
    let i', (tau, theta) =
      Monitor.timer
        (Monitor.function_elaboration, fun () -> Reconstruct.exp' cG apx_i)
    in
    Unify.forceGlobalCnstr ();
    let tau' = Whnf.cnormCTyp (tau, theta) in
    let expression' = Whnf.cnormExp (i', Whnf.m_id) in

    dprintf (fun p ->
        p.fmt "[AFTER Reconstruction Val] @[<v 2>let %a : %a =@ %a@]"
          Identifier.pp identifier
          (P.fmt_ppr_cmp_typ cD P.l0)
          tau'
          (P.fmt_ppr_cmp_exp cD cG P.l0)
          expression');
    let cQ, expression'' =
      Monitor.timer
        (Monitor.function_abstraction, fun () -> Abstract.exp expression')
    in
    add_leftover_vars state cQ location;
    Monitor.timer
      ( Monitor.function_check
      , fun () ->
          Check.Comp.check Option.none cD cG [] expression'' (tau', C.m_id)
      );

    let value_opt =
      if Holes.none () && Context.is_empty cQ then
        Option.some (Opsem.eval expression'')
      else Option.none
    in
    let cid =
      Store.Cid.Comp.add (fun _cid ->
          let mgid =
            Store.Cid.Comp.add_mutual_group
              [ { Synint.Comp.name; tau = tau'; order = `not_recursive } ]
          in
          Store.Cid.Comp.mk_entry name tau' 0 mgid value_opt)
    in
    add_comp_val state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.Val
      { location
      ; identifier
      ; cid
      ; typ = tau'
      ; expression = expression''
      ; expression_value = value_opt
      }

  and reconstruct_typed_val_declaration state location identifier tau
      expression =
    let name = Name.make_from_identifier identifier in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Val at %a" Location.print_short location);
    let apx_tau = index_comp_typ state tau in
    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    let cD, cG = (Synint.LF.Empty, Synint.LF.Empty) in
    let tau' =
      Monitor.timer
        ( Monitor.function_type_elaboration
        , fun () -> Reconstruct.comptyp apx_tau )
    in
    Unify.forceGlobalCnstr ();
    let tau', _ =
      Monitor.timer
        (Monitor.function_type_abstraction, fun () -> Abstract.comptyp tau')
    in
    Monitor.timer
      (Monitor.function_type_check, fun () -> Check.Comp.checkTyp cD tau');
    let apx_i = index_comp_expression state expression in
    let i' =
      Monitor.timer
        ( Monitor.function_elaboration
        , fun () -> Reconstruct.exp cG apx_i (tau', C.m_id) )
    in
    let expression' = Whnf.cnormExp (i', Whnf.m_id) in
    Unify.forceGlobalCnstr ();
    let tau' = Whnf.cnormCTyp (tau', C.m_id) in
    dprintf (fun p ->
        p.fmt "[AFTER Reconstruction Val - 2] let %a : %a =@ %a"
          Identifier.pp identifier
          (P.fmt_ppr_cmp_typ cD P.l0)
          tau'
          (P.fmt_ppr_cmp_exp cD cG P.l0)
          expression');

    let cQ, expression'' =
      Monitor.timer
        (Monitor.function_abstraction, fun () -> Abstract.exp expression')
    in
    add_leftover_vars state cQ location;
    Monitor.timer
      ( Monitor.function_check
      , fun () ->
          Check.Comp.check Option.none cD cG [] expression'' (tau', C.m_id)
      );
    let value_opt =
      if Holes.none () && Context.is_empty cQ then
        Option.some (Opsem.eval expression'')
      else Option.none
    in
    let cid =
      let mgid =
        Store.Cid.Comp.add_mutual_group
          [ { Synint.Comp.name; tau = tau'; order = `not_recursive } ]
      in
      Store.Cid.Comp.add (fun _cid ->
          Store.Cid.Comp.mk_entry name tau' 0 mgid value_opt)
    in
    add_comp_val state ~location identifier cid;
    apply_postponed_fixity_pragmas_for_constant state identifier;
    Synint.Sgn.Val
      { location
      ; identifier
      ; cid
      ; typ = tau'
      ; expression = expression''
      ; expression_value = value_opt
      }

  and reconstruct_query_pragma state location identifier_opt extT
      expected_solutions maximum_tries =
    let name_opt = Option.map Name.make_from_identifier identifier_opt in
    dprintf (fun p ->
        p.fmt "[RecSgn Checking] Query at %a" Location.print_short location);
    let apxT = index_lf_typ state extT in
    dprint (fun () -> "Reconstructing query.");

    Reconstruct.reset_fvarCnstr ();
    Store.FCVar.clear ();
    Store.FVar.clear ();
    let tA =
      Monitor.timer
        ( Monitor.type_elaboration
        , fun () ->
            let tA = Reconstruct.typ Lfrecon.Pi apxT in
            Reconstruct.solve_fvarCnstr Lfrecon.Pi;
            tA )
    in
    dprintf (fun p ->
        p.fmt "Elaboration of query : %a"
          (P.fmt_ppr_lf_typ Synint.LF.Empty Synint.LF.Null P.l0)
          tA);
    Unify.forceGlobalCnstr ();
    let tA', i =
      Monitor.timer (Monitor.type_abstraction, fun () -> Abstract.typ tA)
    in
    Reconstruct.reset_fvarCnstr ();
    Unify.resetGlobalCnstrs ();
    dprintf (fun p ->
        p.fmt
          "Reconstruction (with abstraction) of query: %a with %s \
           abstracted variables"
          (P.fmt_ppr_lf_typ Synint.LF.Empty Synint.LF.Null P.l0)
          tA' (string_of_int i));
    Monitor.timer
      ( Monitor.type_check
      , fun () ->
          Check.LF.checkTyp Synint.LF.Empty Synint.LF.Null (tA', S.LF.id) );
    Logic.storeQuery name_opt (tA', i) Synint.LF.Empty expected_solutions
      maximum_tries;
    Synint.Sgn.Query
      { location
      ; name = identifier_opt
      ; typ = (tA', i)
      ; expected_solutions
      ; maximum_tries
      }

  and reconstruct_module_declaration state location identifier entries =
    let cid = next_module_id state in
    let entries' =
      add_module state ~location identifier cid (fun state ->
          traverse_list state reconstruct_signature_entry entries)
    in
    Synint.Sgn.Module { location; identifier; cid; entries = entries' }

  and reconstruct_recursive_declarations state location declarations =
    let (List1.T (first_declaration, declarations')) = declarations in
    match first_declaration with
    | Synext.Signature.Declaration.Typ _ ->
        let groups =
          group_recursive_lf_typ_declarations first_declaration declarations'
        in
        reconstruct_recursive_lf_typ_declarations state location groups
    | Synext.Signature.Declaration.CompTyp _
    | Synext.Signature.Declaration.CompCotyp _ ->
        let groups =
          group_recursive_comp_typ_declarations first_declaration
            declarations'
        in
        reconstruct_recursive_comp_typ_declarations state location groups
    | Synext.Signature.Declaration.Theorem _
    | Synext.Signature.Declaration.Proof _ ->
        let groups =
          group_recursive_theorem_declarations first_declaration
            declarations'
        in
        reconstruct_recursive_theorem_declarations state location groups
    | Synext.Signature.Declaration.Const _
    | Synext.Signature.Declaration.CompConst _
    | Synext.Signature.Declaration.CompDest _
    | Synext.Signature.Declaration.Schema _
    | Synext.Signature.Declaration.Recursive_declarations _
    | Synext.Signature.Declaration.CompTypAbbrev _
    | Synext.Signature.Declaration.Val _
    | Synext.Signature.Declaration.Module _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and validate_lf_type_and_term_declaration typ_identifier term_constants =
    let typ_qualified_identifier =
      Qualified_identifier.make_simple typ_identifier
    in
    List.iter
      (fun (identifier, typ) ->
        let target = get_lf_typ_target typ in
        if Qualified_identifier.equal typ_qualified_identifier target then ()
        else
          Error.raise_at1
            (Synext.location_of_lf_typ typ)
            (Lf_typ_target_mismatch
               { constant = identifier
               ; expected = typ_identifier
               ; actual = target
               }))
      term_constants

  (** [reconstruct_recursive_lf_typ_declarations location declarations]
      reconstructs the mutually recursive groups of LF type and term constant
      declarations [declarations] located at [location].

      This ideally would proceed as follows:

      + Ensure that the target of each constructor corresponds to the type
        constant for which it is declared.
      + Compute dependency graphs on the type and term constant declarations
        separately.
      + Topologically order these depedency graphs, ensuring that there are
        no dependency cycles.
      + Pre-allocate IDs for the type and term constants, and add them to the
        scope information.
      + Reconstruct the type and term declarations in parallel (inadvisable
        at the moment since the processes involved are not thread-safe).

      For now, we proceed in the naive way of the legacy system, whereby it
      is assumed that the types and terms are already topologically sorted,
      such that we first reconstruct the type declarations, then the term
      declarations. *)
  and reconstruct_recursive_lf_typ_declarations state location declarations =
    List1.iter
      (fun (`Lf_typ (typ_identifier, _kind, term_constants)) ->
        validate_lf_type_and_term_declaration typ_identifier term_constants)
      declarations;
    let typs' =
      traverse_list1 state
        (fun state (`Lf_typ (typ_identifier, kind, _term_constants)) ->
          let location =
            Location.join
              (Identifier.location typ_identifier)
              (Synext.location_of_lf_kind kind)
          in
          reconstruct_lf_typ_declaration state location typ_identifier kind)
        declarations
    in
    let consts' =
      traverse_list1 state
        (fun state (`Lf_typ (_typ_identifier, _kind, term_constants)) ->
          traverse_list state
            (fun state (identifier, typ) ->
              let location =
                Location.join
                  (Identifier.location identifier)
                  (Synext.location_of_lf_typ typ)
              in
              reconstruct_lf_const_declaration state location identifier typ)
            term_constants)
        declarations
    in
    let declarations' =
      List1.map2 (fun typ' consts' -> typ' :: consts') typs' consts'
      |> List1.to_list |> List.flatten |> List1.unsafe_of_list
    in
    Synint.Sgn.Recursive_declarations
      { location; declarations = declarations' }

  and validate_comp_type_and_constructor_declaration typ_identifier
      constructors =
    let typ_qualified_identifier =
      Qualified_identifier.make_simple typ_identifier
    in
    List.iter
      (fun (identifier, typ) ->
        let target = get_comp_typ_target typ in
        if Qualified_identifier.equal typ_qualified_identifier target then ()
        else
          Error.raise_at1
            (Synext.location_of_comp_typ typ)
            (Comp_typ_target_mismatch
               { constant = identifier
               ; expected = typ_identifier
               ; actual = target
               }))
      constructors

  and validate_comp_cotype_and_destructor_declaration typ_identifier
      destructors =
    let typ_qualified_identifier =
      Qualified_identifier.make_simple typ_identifier
    in
    List.iter
      (fun (identifier, observation_typ, _return_typ) ->
        let target = get_comp_cotyp_target observation_typ in
        if Qualified_identifier.equal typ_qualified_identifier target then ()
        else
          Error.raise_at1
            (Synext.location_of_comp_typ observation_typ)
            (Comp_cotyp_target_mismatch
               { constant = identifier
               ; expected = typ_identifier
               ; actual = target
               }))
      destructors

  and reconstruct_recursive_comp_typ_declarations state location declarations
      =
    List1.iter
      (function
        | `Inductive_comp_typ (typ_identifier, _kind, constructors) ->
            validate_comp_type_and_constructor_declaration typ_identifier
              constructors
        | `Stratified_comp_typ (typ_identifier, _kind, constructors) ->
            validate_comp_type_and_constructor_declaration typ_identifier
              constructors
        | `Coinductive_comp_typ (typ_identifier, _kind, destructors) ->
            validate_comp_cotype_and_destructor_declaration typ_identifier
              destructors)
      declarations;
    let typs' =
      traverse_list1 state
        (fun state -> function
          | `Inductive_comp_typ (typ_identifier, kind, _constructors) ->
              let location =
                Location.join
                  (Identifier.location typ_identifier)
                  (Synext.location_of_comp_kind kind)
              in
              reconstruct_comp_typ_constant state location typ_identifier
                kind `Inductive
          | `Stratified_comp_typ (typ_identifier, kind, _constructors) ->
              let location =
                Location.join
                  (Identifier.location typ_identifier)
                  (Synext.location_of_comp_kind kind)
              in
              reconstruct_comp_typ_constant state location typ_identifier
                kind `Stratified
          | `Coinductive_comp_typ (typ_identifier, kind, _destructors) ->
              let location =
                Location.join
                  (Identifier.location typ_identifier)
                  (Synext.location_of_comp_kind kind)
              in
              reconstruct_comp_cotyp_constant state location typ_identifier
                kind)
        declarations
    in
    let consts' =
      traverse_list1 state
        (fun state -> function
          | `Inductive_comp_typ (_typ_identifier, _kind, constructors)
          | `Stratified_comp_typ (_typ_identifier, _kind, constructors) ->
              let stratNum =
                ref (-1)
                (* This is inherited from the legacy system. This is an array
                   with length equal to the number of explicit arguments in
                   [_kind], and whose values are all [true]. Reconstruction
                   of constructors in the [`Stratified_comp_typ] case mutates
                   this value. *)
              in
              traverse_list state
                (fun state (identifier, typ) ->
                  let location =
                    Location.join
                      (Identifier.location identifier)
                      (Synext.location_of_comp_typ typ)
                  in
                  reconstruct_comp_constructor state ~stratNum location
                    identifier typ)
                constructors
          | `Coinductive_comp_typ (_typ_identifier, _kind, destructors) ->
              traverse_list state
                (fun state (identifier, observation_typ, return_typ) ->
                  let location =
                    Location.join
                      (Identifier.location identifier)
                      (Location.join
                         (Synext.location_of_comp_typ observation_typ)
                         (Synext.location_of_comp_typ return_typ))
                  in
                  reconstruct_comp_destructor state location identifier
                    observation_typ return_typ)
                destructors)
        declarations
    in
    let declarations' =
      List1.map2 (fun typ' consts' -> typ' :: consts') typs' consts'
      |> List1.to_list |> List.flatten |> List1.unsafe_of_list
    in
    Synint.Sgn.Recursive_declarations
      { location; declarations = declarations' }

  and translate_totality_order :
        'a.
        'a Synext.signature_totality_order -> 'a Synint.Comp.generic_order =
    function
    | Synext.Signature.Totality.Order.Argument { argument; _ } ->
        Synint.Comp.Arg argument
    | Synext.Signature.Totality.Order.Lexical_ordering { arguments; _ } ->
        let arguments' = List1.map translate_totality_order arguments in
        Synint.Comp.Lex (List1.to_list arguments')
    | Synext.Signature.Totality.Order.Simultaneous_ordering { arguments; _ }
      ->
        let arguments' = List1.map translate_totality_order arguments in
        Synint.Comp.Simul (List1.to_list arguments')

  and reconstruct_totality_declaration program typ declaration =
    match declaration with
    | Synext.Signature.Totality.Declaration.Trust _ -> `trust
    | Synext.Signature.Totality.Declaration.Numeric { order; _ } -> (
        match order with
        | Option.None -> `not_recursive
        | Option.Some order ->
            `inductive
              (Reconstruct.numeric_order typ
                 (translate_totality_order order)))
    | Synext.Signature.Totality.Declaration.Named
        { location; order; program = program'; argument_labels } -> (
        if
          (* Validate the inputs: can't have too many args or the wrong
             name *)
          Bool.not (Total.is_valid_args typ (List.length argument_labels))
        then
          Error.raise_at1 location
            (Too_many_totality_declaration_arguments program)
        else if Identifier.(program <> program') then
          Error.raise_at1 location
            (Totality_declaration_program_mismatch
               { expected_program = program; actual_program = program' })
        else
          match order with
          | Option.None -> `not_recursive
          | Option.Some order ->
              (* Reconstruct to a numeric order by looking up the positions
                 of the specified arguments. *)
              let order' =
                Synint.Comp.map_order
                  (fun x ->
                    match
                      List.index_of
                        (Option.equal Identifier.equal (Option.some x))
                        argument_labels
                    with
                    | Option.None ->
                        Error.raise_at1 location
                          (Unbound_totality_declaration_argument
                             { unbound_argument = x
                             ; arguments = argument_labels
                             })
                    | Option.Some k ->
                        k + 1 (* index_of is 0-based, but we're 1-based *))
                  (translate_totality_order order)
              in
              `inductive order')

  (** [guard_totality_declarations location declarations] collects the
      totality declarations in [declarations] and ensures that either:

      - each declaration in [declarations] has a totality declaration, or
      - no declaration in [declarations] has a totality declaration.

      [location] is the location of the mutually recursive group of
      declarations [declarations], and is used for error-reporting. *)
  and guard_totality_declarations location declarations =
    match
      List1.partition_map
        (function
          | `Proof (identifier, _, totality_declaration_opt, _)
          | `Theorem (identifier, _, totality_declaration_opt, _) -> (
              match totality_declaration_opt with
              | Option.None -> Either.left identifier
              | Option.Some totality_declaration ->
                  Either.right (identifier, totality_declaration)))
        declarations
    with
    | Either.Right ([], haves) ->
        (* All the program declarations have a totality declaration *)
        Option.some (List1.map Pair.snd haves)
    | Either.Left (_have_nots, []) ->
        (* All the program declarations don't have a totality declaration *)
        Option.none
    | Either.Right (have_nots, haves) ->
        Error.raise_at1 location
          (Missing_totality_declarations
             { programs_with = List1.to_list (List1.map Pair.fst haves)
             ; programs_without = have_nots
             })
    | Either.Left (have_nots, haves) ->
        Error.raise_at1 location
          (Missing_totality_declarations
             { programs_with = List.map Pair.fst haves
             ; programs_without = List1.to_list have_nots
             })

  and reconstruct_recursive_theorem_declarations state location declarations
      =
    let reconstruct_program_typ state typ =
      let apx_tau = index_comp_typ state typ in
      Reconstruct.reset_fvarCnstr ();
      Store.FCVar.clear ();
      let tau' =
        Monitor.timer
          ( Monitor.function_type_elaboration
          , fun () -> Reconstruct.comptyp apx_tau )
      in
      Unify.forceGlobalCnstr ();
      (* Are some FMVars delayed since we can't infer their type? - Not
         associated with pattsub *)
      let tau', _ =
        Monitor.timer
          (Monitor.function_type_abstraction, fun () -> Abstract.comptyp tau')
      in
      Monitor.timer
        ( Monitor.function_type_check
        , fun () -> Check.Comp.checkTyp Synint.LF.Empty tau' );
      Store.FCVar.clear ();

      tau'
    in

    let register_program state identifier tau' total_decs =
      let name = Name.make_from_identifier identifier in
      let cid =
        Store.Cid.Comp.add (fun _cid ->
            Store.Cid.Comp.mk_entry name tau' 0 total_decs Option.none)
      in
      add_prog state identifier cid;
      apply_postponed_fixity_pragmas_for_constant state identifier;
      cid
    in

    let total_decs = guard_totality_declarations location declarations in

    let preprocess state =
      traverse_list1 state (fun state -> function
        | `Proof (identifier, typ, _totality_declaration_opt, body) ->
            let tau' = reconstruct_program_typ state typ in
            ( (identifier, `Proof body, location, tau')
            , fun state -> register_program state identifier tau' )
        | `Theorem (identifier, typ, _totality_declaration_opt, body) ->
            let tau' = reconstruct_program_typ state typ in
            ( (identifier, `Theorem body, location, tau')
            , fun state -> register_program state identifier tau' ))
    in

    let thm_list, registers = List1.split (preprocess state declarations) in

    (* We have the elaborated types of the theorems, so we construct the
       final list of totality declarations for this mutual group. *)
    let total_decs =
      match total_decs with
      | Option.Some total_decs ->
          List1.map2
            (fun (thm_name, _, _, tau) decl ->
              reconstruct_totality_declaration thm_name tau decl
              |> Synint.Comp.make_total_dec
                   (Name.make_from_identifier thm_name)
                   tau)
            thm_list total_decs
      | Option.None ->
          List1.map
            (fun (thm_name, _, _, tau) ->
              Synint.Comp.make_total_dec
                (Name.make_from_identifier thm_name)
                tau `partial)
            thm_list
    in

    (* We have the list of all totality declarations for this group, so we
       can register each theorem in the store. *)
    let thm_cid_list =
      traverse_list1 state
        (fun state register ->
          let cid =
            Store.Cid.Comp.add_mutual_group (List1.to_list total_decs)
          in
          register state cid)
        registers
    in

    let reconThm state loc (f, cid, thm, tau) =
      let name = Name.make_from_identifier f in
      let apx_thm =
        match thm with
        | `Proof p -> index_harpoon_proof state p
        | `Theorem p -> index_comp_theorem state p
      in
      dprint (fun () -> "[reconThm] Indexing theorem done.");
      let thm' =
        Monitor.timer
          ( Monitor.function_elaboration
          , fun () ->
              Reconstruct.thm Synint.LF.Empty apx_thm
                (Total.strip tau, C.m_id) )
      in
      dprintf (fun p ->
          p.fmt
            "[reconThm] @[<v>Elaboration of theorem %a : %a@,\
             result: @[%a@]@]" Identifier.pp f
            (P.fmt_ppr_cmp_typ Synint.LF.Empty P.l0)
            tau P.fmt_ppr_cmp_thm thm');
      (try Unify.forceGlobalCnstr () with
      | Unify.GlobalCnstrFailure (loc, cnstr) ->
          raise
            (Check.Comp.Error
               ( loc
               , Check.Comp.UnsolvableConstraints (Option.some name, cnstr)
               )));

      Unify.resetGlobalCnstrs ();

      dprintf (fun p ->
          p.fmt "[AFTER reconstruction] @[<v>Function %a : %a@,@[%a@]@]"
            Identifier.pp f
            (P.fmt_ppr_cmp_typ Synint.LF.Empty P.l0)
            tau P.fmt_ppr_cmp_thm thm');

      let thm'' = Whnf.cnormThm (thm', Whnf.m_id) in
      let cQ, thm_r =
        Monitor.timer
          (Monitor.function_abstraction, fun () -> Abstract.thm thm'')
      in
      add_leftover_vars state cQ location;

      (* This abstraction is for detecting leftover metavariables, which is
         an error. *)
      let thm_r' = Whnf.cnormThm (thm_r, Whnf.m_id) in

      let tau_ann =
        match Total.lookup_dec name (List1.to_list total_decs) with
        | Option.None -> tau
        | Option.Some d ->
            let tau = Total.annotate loc d.Synint.Comp.order tau in
            dprintf (fun p ->
                p.fmt "[reconThm] @[<v>got annotated type:@,@[%a@]@]"
                  P.(fmt_ppr_cmp_typ Synint.LF.Empty l0)
                  tau);
            tau
      in
      Monitor.timer
        ( Monitor.function_check
        , fun () ->
            dprintf (fun p ->
                p.fmt
                  "[recThm] @[<v>begin checking theorem %a.@,\
                   @[<hv 2>total_decs =@ @[<v>%a@]@]@,\
                   tau_ann = @[%a@]@]" Identifier.pp f
                  (List1.pp ~pp_sep:Format.pp_print_cut
                     P.(fmt_ppr_cmp_total_dec))
                  total_decs
                  P.(fmt_ppr_cmp_typ Synint.LF.Empty l0)
                  tau_ann);
            Total.enabled :=
              Total.requires_checking name (List1.to_list total_decs);
            Check.Comp.thm (Some cid) Synint.LF.Empty Synint.LF.Empty
              (List1.to_list total_decs)
              thm_r' (tau_ann, C.m_id);
            Total.enabled := false );
      (thm_r', tau)
    in

    let ds =
      let reconOne state
          (thm_cid, (thm_identifier, thm_body, thm_location, thm_typ)) =
        let e_r', tau' =
          reconThm state thm_location
            (thm_identifier, thm_cid, thm_body, thm_typ)
        in
        dprintf (fun p ->
            p.fmt
              "[reconRecFun] @[<v>DOUBLE CHECK of function %a at %a \
               successful@,\
               Adding definition to the store.@]" Identifier.pp
              thm_identifier Location.print_short thm_location);
        let v =
          Synint.Comp.ThmValue
            (thm_cid, e_r', Synint.LF.MShift 0, Synint.Comp.Empty)
        in
        Store.Cid.Comp.set_prog thm_cid (Fun.const (Option.some v));
        Synint.Sgn.Theorem
          { identifier = thm_identifier
          ; cid = thm_cid
          ; body = e_r'
          ; location = thm_location
          ; typ = tau'
          }
      in
      traverse_list1 state reconOne (List1.combine thm_cid_list thm_list)
    in
    Synint.Sgn.Recursive_declarations { location; declarations = ds }

  and group_recursive_lf_typ_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.Typ { identifier; kind; _ } -> (
        let lf_term_constant_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.Const { identifier; typ; _ } ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let lf_typ_declaration =
          `Lf_typ (identifier, kind, lf_term_constant_declarations)
        in
        match declarations' with
        | [] -> List1.singleton lf_typ_declaration
        | first_declaration' :: declarations'' ->
            let lf_typ_declarations =
              group_recursive_lf_typ_declarations first_declaration'
                declarations''
            in
            List1.cons lf_typ_declaration lf_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_theorem_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.Theorem
        { identifier; typ; order; body; _ } -> (
        let theorem_declaration = `Theorem (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton theorem_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons theorem_declaration theorem_declarations)
    | Synext.Signature.Declaration.Proof { identifier; typ; order; body; _ }
      -> (
        let proof_declaration = `Proof (identifier, typ, order, body) in
        match declarations with
        | [] -> List1.singleton proof_declaration
        | first_declaration' :: declarations'' ->
            let theorem_declarations =
              group_recursive_theorem_declarations first_declaration'
                declarations''
            in
            List1.cons proof_declaration theorem_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration

  and group_recursive_comp_typ_declarations first_declaration declarations =
    match first_declaration with
    | Synext.Signature.Declaration.CompTyp
        { identifier; kind; datatype_flavour; _ } -> (
        let comp_constructor_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.CompConst { identifier; typ; _ }
                ->
                  Option.some (identifier, typ)
              | _ -> Option.none)
            declarations
        in
        let comp_typ_declaration =
          match datatype_flavour with
          | `Inductive ->
              `Inductive_comp_typ
                (identifier, kind, comp_constructor_declarations)
          | `Stratified ->
              `Stratified_comp_typ
                (identifier, kind, comp_constructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_typ_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_typ_declaration comp_typ_declarations)
    | Synext.Signature.Declaration.CompCotyp { identifier; kind; _ } -> (
        let comp_destructor_declarations, declarations' =
          List.take_while_map
            (function
              | Synext.Signature.Declaration.CompDest
                  { identifier; observation_type; return_type; _ } ->
                  Option.some (identifier, observation_type, return_type)
              | _ -> Option.none)
            declarations
        in
        let comp_cotyp_declaration =
          `Coinductive_comp_typ
            (identifier, kind, comp_destructor_declarations)
        in
        match declarations' with
        | [] -> List1.singleton comp_cotyp_declaration
        | first_declaration' :: declarations'' ->
            let comp_typ_declarations =
              group_recursive_comp_typ_declarations first_declaration'
                declarations''
            in
            List1.cons comp_cotyp_declaration comp_typ_declarations)
    | _ ->
        Error.raise_at1
          (Synext.location_of_signature_declaration first_declaration)
          Unsupported_recursive_declaration
end

module Signature_reconstruction =
  Make (Recsgn_state.Signature_reconstruction_state)
