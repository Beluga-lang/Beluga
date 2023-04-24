open Syncom
open Synext_definition

(** {1 LF} *)

val location_of_lf_kind : lf_kind -> Location.t

val location_of_lf_typ : lf_typ -> Location.t

val location_of_lf_term : lf_term -> Location.t

(** {1 Contextual LF} *)

val location_of_clf_typ : clf_typ -> Location.t

val location_of_clf_term : clf_term -> Location.t

val location_of_clf_substitution : clf_substitution -> Location.t

val location_of_clf_substitution_pattern :
  clf_substitution_pattern -> Location.t

val location_of_clf_context : clf_context -> Location.t

val location_of_clf_context_pattern : clf_context_pattern -> Location.t

val location_of_clf_term_pattern : clf_term_pattern -> Location.t

(** {1 Meta-Level} *)

val location_of_meta_type : meta_typ -> Location.t

val location_of_meta_object : meta_object -> Location.t

val location_of_meta_object_pattern : meta_pattern -> Location.t

val location_of_meta_context : meta_context -> Location.t

val location_of_schema : schema -> Location.t

(** {1 Computation-Level} *)

val location_of_comp_kind : comp_kind -> Location.t

val location_of_comp_typ : comp_typ -> Location.t

val location_of_comp_expression : comp_expression -> Location.t

val location_of_comp_case_branch : comp_case_branch -> Location.t

val location_of_comp_cofunction_branch : comp_cofunction_branch -> Location.t

val location_of_comp_pattern : comp_pattern -> Location.t

val location_of_comp_copattern : comp_copattern -> Location.t

(** {1 Harpoon} *)

val location_of_harpoon_proof : harpoon_proof -> Location.t

val location_of_harpoon_command : harpoon_command -> Location.t

val location_of_harpoon_directive : harpoon_directive -> Location.t

val location_of_harpoon_split_branch : harpoon_split_branch -> Location.t

val location_of_harpoon_split_branch_label :
  harpoon_split_branch_label -> Location.t

val location_of_harpoon_suffices_branch :
  harpoon_suffices_branch -> Location.t

val location_of_harpoon_hypothetical : harpoon_hypothetical -> Location.t

val location_of_harpoon_repl_command : harpoon_repl_command -> Location.t

(** {1 Signature} *)

val location_of_signature_pragma : signature_pragma -> Location.t

val location_of_signature_global_pragma :
  signature_global_pragma -> Location.t

val location_of_signature_totality_declaration :
  signature_totality_declaration -> Location.t

val location_of_signature_totality_order :
  'a signature_totality_order -> Location.t

val location_of_signature_entry : signature_entry -> Location.t

val location_of_signature_declaration : signature_declaration -> Location.t
