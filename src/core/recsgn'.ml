open Support
open Beluga_syntax
module Synint = Syntax.Int

[@@@warning "+A-4-44"]

exception Dangling_not_pragma

exception Unexpected_entry_reconstruction_success

let () =
  Error.register_exception_printer (function
    | Dangling_not_pragma ->
        Format.dprintf "%a" Format.pp_print_text
          "This `--not' pragma must precede some signature entry."
    | Unexpected_entry_reconstruction_success ->
        Format.dprintf "%a" Format.pp_print_text
          "This signature entry was successfully reconstructed, but the \
           `--not' pragma indicates that it was expected to fail \
           reconstruction."
    | exn -> Error.raise_unsupported_exception_printing exn)

module type SIGNATURE_RECONSTRUCTION_STATE = sig
  include State.STATE

  val get_leftover_vars :
    (Abstract.free_var Synint.LF.ctx * Location.t) List.t t

  val add_leftover_vars :
    Abstract.free_var Synint.LF.ctx -> Location.t -> Unit.t t

  (** [disable_lf_strengthening ~location] disables the strengthening of LF
      terms and types during LF reconstruction.

      [location] is the location to use for error-reporting in case of
      failure to perform [disable_lf_strengthening ~location]. *)
  val disable_lf_strengthening : location:Location.t -> Unit.t t

  (** [enable_warn_on_coverage_error ~location] sets the error-reporting mode
      of pattern coverage-checking to `warn'.

      [location] is the location to use for error-reporting in case of
      failure to perform [enable_warn_on_coverage_error ~location]. *)
  val enable_warn_on_coverage_error : location:Location.t -> Unit.t t

  (** [enable_raise_on_coverage_error ~location] sets the error-reporting
      mode of pattern coverage-checking to `raise'.

      [location] is the location to use for error-reporting in case of
      failure to perform [enable_raise_on_coverage_error ~location]. *)
  val enable_raise_on_coverage_error : location:Location.t -> Unit.t t

  (** [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant]
      sets the naming convention for name generation of meta-level and
      computation-level variables using [meta_variable_base] and
      [computation_variable_base] respectively for a type-level constant
      [constant].

      [location] is the location to use for error-reporting in case of
      failure to perform
      [set_name_generation_bases ~location ~meta_variable_base ?computation_variable_base constant].*)
  val set_name_generation_bases :
       location:Location.t
    -> meta_variable_base:Identifier.t
    -> ?computation_variable_base:Identifier.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_default_associativity :
    location:Location.t -> Associativity.t -> Unit.t t

  val set_operator_prefix :
       location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_infix :
       location:Location.t
    -> ?precedence:Int.t
    -> ?associativity:Associativity.t
    -> Qualified_identifier.t
    -> Unit.t t

  val set_operator_postfix :
       location:Location.t
    -> ?precedence:Int.t
    -> Qualified_identifier.t
    -> Unit.t t

  val open_module : location:Location.t -> Qualified_identifier.t -> Unit.t t

  val add_module_abbreviation :
       location:Location.t
    -> Qualified_identifier.t
    -> abbreviation:Identifier.t
    -> Unit.t t

  val with_checkpoint : 'a t -> 'a t
end

module type SIGNATURE_RECONSTRUCTION = sig
  include State.STATE

  val reconstruct_signature : Synext.signature -> Synint.Sgn.sgn t
end

module Make (Signature_reconstruction_state : SIGNATURE_RECONSTRUCTION_STATE) :
  SIGNATURE_RECONSTRUCTION
    with type state = Signature_reconstruction_state.state = struct
  include Signature_reconstruction_state

  let rec reconstruct_signature signature =
    let { Synext.Signature.global_pragmas; entries } = signature in
    let* () = apply_global_pragmas global_pragmas in
    reconstruct_signature_entries entries

  and apply_global_pragmas global_pragmas =
    traverse_list_void apply_global_pragma global_pragmas

  and apply_global_pragma global_pragma =
    match global_pragma with
    | Synext.Signature.Global_pragma.No_strengthening { location } ->
        disable_lf_strengthening ~location
    | Synext.Signature.Global_pragma.Warn_on_coverage_error { location } ->
        enable_warn_on_coverage_error ~location
    | Synext.Signature.Global_pragma.Raise_error_on_coverage_error
        { location } ->
        enable_raise_on_coverage_error ~location

  (** [reconstruct_signature_entries entries] reconstructs a list of
      signature entries. This in particular handles the reconstruction of
      entries that are not handled independently from one another, such as
      [--not] pragmas. *)
  and reconstruct_signature_entries entries =
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
            let* entry_res' =
              try_catch_lazy
                (lazy
                  ( with_checkpoint (reconstruct_signature_entry entry)
                  $> fun entry' -> Result.ok entry' ))
                ~on_exn:(fun reconstruction_error ->
                  (* The [--not] pragma was used properly *)
                  return (Result.error reconstruction_error))
            in
            match entry_res' with
            | Result.Ok _ ->
                Error.raise_at2 pragma_location
                  (Synext.location_of_signature_entry entry)
                  Unexpected_entry_reconstruction_success
            | Result.Error _ ->
                Chatter.print 1
                  "Reconstruction fails for --not'd declaration@.";
                reconstruct_signature_entries entries))
    | entry :: entries ->
        let* entry' = reconstruct_signature_entry entry in
        let* entries' = reconstruct_signature_entries entries in
        return (entry' :: entries')
    | [] -> return []

  (** [reconstruct_signature_entry entry] reconstructs a single signature
      entry. *)
  and reconstruct_signature_entry entry =
    match entry with
    | Synext.Signature.Entry.Comment { location; content } ->
        return (Synint.Sgn.Comment { location; content })
    | Synext.Signature.Entry.Pragma { pragma; _ } ->
        reconstruct_signature_pragma pragma
    | Synext.Signature.Entry.Declaration { declaration; _ } ->
        reconstruct_signature_declaration declaration

  and reconstruct_signature_pragma pragma =
    match pragma with
    | Synext.Signature.Pragma.Not _ ->
        Error.raise_violation
          "[reconstruct_signature_pragma] --not pragma must be \
           reconstructed with [reconstruct_signature_entries]"
    | Synext.Signature.Pragma.Name
        { location; constant; meta_variable_base; computation_variable_base }
      ->
        let* () =
          set_name_generation_bases ~location ~meta_variable_base
            ?computation_variable_base constant
        in
        let name = Name.make_from_qualified_identifier constant in
        return (Synint.Sgn.Pragma { pragma = Synint.LF.NamePrag name })
    | Synext.Signature.Pragma.Default_associativity
        { associativity; location } ->
        let* () = set_default_associativity ~location associativity in
        return
          (Synint.Sgn.Pragma
             { pragma = Synint.LF.DefaultAssocPrag associativity })
    | Synext.Signature.Pragma.Prefix_fixity
        { location; constant; precedence } ->
        let* () = set_operator_prefix ~location ?precedence constant in
        let name = Name.make_from_qualified_identifier constant in
        let associativity = Option.some Associativity.right_associative in
        return
          (Synint.Sgn.Pragma
             { pragma =
                 Synint.LF.FixPrag
                   (name, Fixity.prefix, precedence, associativity)
             })
    | Synext.Signature.Pragma.Infix_fixity
        { location; constant; precedence; associativity } ->
        let* () =
          set_operator_infix ~location ?precedence ?associativity constant
        in
        let name = Name.make_from_qualified_identifier constant in
        return
          (Synint.Sgn.Pragma
             { pragma =
                 Synint.LF.FixPrag
                   (name, Fixity.infix, precedence, associativity)
             })
    | Synext.Signature.Pragma.Postfix_fixity
        { location; constant; precedence } ->
        let* () = set_operator_postfix ~location ?precedence constant in
        let name = Name.make_from_qualified_identifier constant in
        let associativity = Option.some Associativity.left_associative in
        return
          (Synint.Sgn.Pragma
             { pragma =
                 Synint.LF.FixPrag
                   (name, Fixity.postfix, precedence, associativity)
             })
    | Synext.Signature.Pragma.Open_module { location; module_identifier } ->
        let* () = open_module ~location module_identifier in
        return
          (Synint.Sgn.Pragma
             { pragma = Synint.LF.OpenPrag module_identifier })
    | Synext.Signature.Pragma.Abbreviation
        { location; module_identifier; abbreviation } ->
        let* () =
          add_module_abbreviation ~location module_identifier ~abbreviation
        in
        let module_identifier_as_list =
          module_identifier |> Qualified_identifier.to_list1 |> List1.to_list
          |> List.map Identifier.show
        in
        return
          (Synint.Sgn.Pragma
             { pragma =
                 Synint.LF.AbbrevPrag
                   (module_identifier_as_list, Identifier.show abbreviation)
             })

  and reconstruct_signature_declaration declaration =
    match declaration with
    | Synext.Signature.Declaration.CompTyp { location; _ }
    | Synext.Signature.Declaration.CompCotyp { location; _ }
    | Synext.Signature.Declaration.CompConst { location; _ }
    | Synext.Signature.Declaration.CompDest { location; _ }
    | Synext.Signature.Declaration.Theorem { location; _ }
    | Synext.Signature.Declaration.Proof { location; _ } ->
        Error.raise_violation ~location
          "[reconstruct_signature_declaration] this kind of signature \
           declaration is only supported within a mutually recursive group \
           of declarations."
    | Synext.Signature.Declaration.Typ _ -> Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Const _ -> Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Schema _ -> Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.CompTypAbbrev _ ->
        Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Val _ -> Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Query _ -> Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Recursive_declarations _ ->
        Obj.magic () (* TODO: *)
    | Synext.Signature.Declaration.Module _ -> Obj.magic () (* TODO: *)
end
