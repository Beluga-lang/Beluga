(** Pretty-printing for the external syntax. *)

open Synext_definition

(** {1 LF} *)

val pp_lf_kind : Format.formatter -> lf_kind -> unit

val pp_lf_typ : Format.formatter -> lf_typ -> unit

val pp_lf_term : Format.formatter -> lf_term -> unit

(** {1 Contextual LF} *)

val pp_clf_typ : Format.formatter -> clf_typ -> unit

val pp_clf_term : Format.formatter -> clf_term -> unit

val pp_clf_term_pattern : Format.formatter -> clf_term_pattern -> unit

val pp_clf_substitution : Format.formatter -> clf_substitution -> unit

val pp_clf_substitution_pattern :
  Format.formatter -> clf_substitution_pattern -> unit

val pp_clf_context : Format.formatter -> clf_context -> unit

val pp_clf_context_pattern : Format.formatter -> clf_context_pattern -> unit

(** {1 Meta-Level} *)

val pp_meta_typ : Format.formatter -> meta_typ -> unit

val pp_meta_object : Format.formatter -> meta_object -> unit

val pp_meta_context : Format.formatter -> meta_context -> unit

val pp_meta_pattern : Format.formatter -> meta_pattern -> unit

val pp_schema : Format.formatter -> schema -> unit

(** {1 Computation-Level} *)

val pp_comp_kind : Format.formatter -> comp_kind -> unit

val pp_comp_typ : Format.formatter -> comp_typ -> unit

val pp_comp_expression : Format.formatter -> comp_expresion -> unit

val pp_comp_pattern : Format.formatter -> comp_pattern -> unit

val pp_comp_copattern : Format.formatter -> comp_copattern -> unit

val pp_comp_context : Format.formatter -> comp_context -> unit

(** {1 Harpoon} *)

val pp_harpoon_proof : Format.formatter -> harpoon_proof -> unit

val pp_harpoon_command : Format.formatter -> harpoon_command -> unit

val pp_harpoon_directive : Format.formatter -> harpoon_directive -> unit

val pp_harpoon_hypothetical :
  Format.formatter -> harpoon_hypothetical -> unit

val pp_harpoon_repl_command :
  Format.formatter -> harpoon_repl_command -> unit

(** {1 Signature} *)

val pp_signature_pragma : Format.formatter -> signature_pragma -> unit

val pp_signature_global_pragma :
  Format.formatter -> signature_global_pragma -> unit

val pp_signature_totality_declaration :
  Format.formatter -> signature_totality_declaration -> unit

val pp_signature_declaration :
  Format.formatter -> signature_declaration -> unit

val pp_signature_signature : Format.formatter -> signature -> unit
