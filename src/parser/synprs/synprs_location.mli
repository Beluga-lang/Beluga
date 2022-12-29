open Beluga_syntax
open Synprs_definition

(** {1 LF} *)

val location_of_lf_object : lf_object -> Location.t

val set_location_of_lf_object : Location.t -> lf_object -> lf_object

(** {1 Contextual LF} *)

val location_of_clf_object : clf_object -> Location.t

val set_location_of_clf_object : Location.t -> clf_object -> clf_object

val location_of_clf_context_object : clf_context_object -> Location.t

(** {1 Meta-Level} *)

val location_of_meta_thing : meta_thing -> Location.t

val location_of_schema_object : schema_object -> Location.t

val location_of_meta_context_object : meta_context_object -> Location.t

(** {1 Computation-Level} *)

val location_of_comp_sort_object : comp_sort_object -> Location.t

val set_location_of_comp_sort_object :
  Location.t -> comp_sort_object -> comp_sort_object

val location_of_comp_expression_object : comp_expression_object -> Location.t

val set_location_of_comp_expression_object :
  Location.t -> comp_expression_object -> comp_expression_object

val location_of_comp_pattern_object : comp_pattern_object -> Location.t

val set_location_of_comp_pattern_object :
  Location.t -> comp_pattern_object -> comp_pattern_object

val location_of_comp_context_object : comp_context_object -> Location.t

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

val location_of_signature_declaration : signature_declaration -> Location.t
