open Support
open Beluga_syntax
open Synext

(** {1 Common} *)

val json_of_identifier : Identifier.t -> Yojson.Safe.t

val json_of_qualified_identifier : Qualified_identifier.t -> Yojson.Safe.t

val json_of_identifier_opt : Identifier.t Option.t -> Yojson.Safe.t

val json_of_qualified_identifier_opt :
  Qualified_identifier.t Option.t -> Yojson.Safe.t

val json_of_location : Location.t -> Yojson.Safe.t

val json_of_plicity : Plicity.t -> Yojson.Safe.t

val json_of_fixity : Fixity.t -> Yojson.Safe.t

val json_of_associativity : Associativity.t -> Yojson.Safe.t

val json_of_operator : Operator.t -> Yojson.Safe.t

(** {1 LF} *)

val json_of_lf_kind : lf_kind -> Yojson.Safe.t

val json_of_lf_typ : lf_typ -> Yojson.Safe.t

val json_of_lf_term : lf_term -> Yojson.Safe.t

(** {1 Contextual LF} *)

val json_of_clf_typ : clf_typ -> Yojson.Safe.t

val json_of_clf_term : clf_term -> Yojson.Safe.t

val json_of_clf_term_pattern : clf_term_pattern -> Yojson.Safe.t

val json_of_clf_substitution : clf_substitution -> Yojson.Safe.t

val json_of_clf_substitution_head : CLF.Substitution.Head.t -> Yojson.Safe.t

val json_of_clf_substitution_pattern :
  clf_substitution_pattern -> Yojson.Safe.t

val json_of_clf_substitution_pattern_head :
  CLF.Substitution.Pattern.Head.t -> Yojson.Safe.t

val json_of_clf_context : clf_context -> Yojson.Safe.t

val json_of_clf_context_head : CLF.Context.Head.t -> Yojson.Safe.t

val json_of_clf_context_pattern : clf_context_pattern -> Yojson.Safe.t

val json_of_clf_context_pattern_head :
  CLF.Context.Pattern.Head.t -> Yojson.Safe.t

(** {1 Meta-Level} *)

val json_of_meta_typ : meta_typ -> Yojson.Safe.t

val json_of_meta_object : meta_object -> Yojson.Safe.t

val json_of_meta_pattern : meta_pattern -> Yojson.Safe.t

val json_of_meta_context : meta_context -> Yojson.Safe.t

val json_of_schema : schema -> Yojson.Safe.t

(** {1 Computation-Level} *)

val json_of_comp_kind : comp_kind -> Yojson.Safe.t

val json_of_comp_typ : comp_typ -> Yojson.Safe.t

val json_of_comp_expression : comp_expression -> Yojson.Safe.t

val json_of_comp_pattern : comp_pattern -> Yojson.Safe.t

val json_of_comp_copattern : comp_copattern -> Yojson.Safe.t

val json_of_comp_context : comp_context -> Yojson.Safe.t

(** {1 Harpoon} *)

val json_of_harpoon_proof : harpoon_proof -> Yojson.Safe.t

val json_of_harpoon_command : harpoon_command -> Yojson.Safe.t

val json_of_harpoon_directive : harpoon_directive -> Yojson.Safe.t

val json_of_harpoon_split_branch : harpoon_split_branch -> Yojson.Safe.t

val json_of_harpoon_split_branch_label :
  harpoon_split_branch_label -> Yojson.Safe.t

val json_of_harpoon_suffices_branch :
  harpoon_suffices_branch -> Yojson.Safe.t

val json_of_harpoon_hypothetical : harpoon_hypothetical -> Yojson.Safe.t

val json_of_harpoon_repl_command : harpoon_repl_command -> Yojson.Safe.t

(** {1 Signature} *)

val json_of_signature_pragma : signature_pragma -> Yojson.Safe.t

val json_of_signature_global_pragma :
  signature_global_pragma -> Yojson.Safe.t

val json_of_signature_totality_declaration :
  signature_totality_declaration -> Yojson.Safe.t

val json_of_signature_numeric_totality_order :
  int signature_totality_order -> Yojson.Safe.t

val json_of_signature_named_totality_order :
  Identifier.t signature_totality_order -> Yojson.Safe.t

val json_of_signature_declaration : signature_declaration -> Yojson.Safe.t

val json_of_signature_file : signature_file -> Yojson.Safe.t

val json_of_signature : signature -> Yojson.Safe.t
