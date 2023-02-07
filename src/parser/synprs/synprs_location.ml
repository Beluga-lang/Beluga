open Synprs_definition

(** {1 LF} *)

let location_of_lf_object object_ =
  let open LF.Object in
  match object_ with
  | Raw_identifier { location; _ }
  | Raw_qualified_identifier { location; _ }
  | Raw_type { location; _ }
  | Raw_hole { location; _ }
  | Raw_pi { location; _ }
  | Raw_lambda { location; _ }
  | Raw_arrow { location; _ }
  | Raw_annotated { location; _ }
  | Raw_application { location; _ } ->
      location

let[@warning "-23"] set_location_of_lf_object location object_ =
  let open LF.Object in
  match object_ with
  | Raw_identifier o -> Raw_identifier { o with location }
  | Raw_qualified_identifier o ->
      Raw_qualified_identifier { o with location }
  | Raw_type o -> Raw_type { o with location }
  | Raw_hole o -> Raw_hole { o with location }
  | Raw_pi o -> Raw_pi { o with location }
  | Raw_lambda o -> Raw_lambda { o with location }
  | Raw_arrow o -> Raw_arrow { o with location }
  | Raw_annotated o -> Raw_annotated { o with location }
  | Raw_application o -> Raw_application { o with location }

(** {1 Contextual LF} *)

let location_of_clf_object object_ =
  let open CLF.Object in
  match object_ with
  | Raw_identifier { location; _ }
  | Raw_qualified_identifier { location; _ }
  | Raw_hole { location; _ }
  | Raw_pi { location; _ }
  | Raw_lambda { location; _ }
  | Raw_arrow { location; _ }
  | Raw_annotated { location; _ }
  | Raw_application { location; _ }
  | Raw_block { location; _ }
  | Raw_tuple { location; _ }
  | Raw_projection { location; _ }
  | Raw_substitution { location; _ } ->
      location

let[@warning "-23"] set_location_of_clf_object location
    (object_ : clf_object) =
  let open CLF.Object in
  match object_ with
  | Raw_identifier o -> Raw_identifier { o with location }
  | Raw_qualified_identifier o ->
      Raw_qualified_identifier { o with location }
  | Raw_hole o -> Raw_hole { o with location }
  | Raw_pi o -> Raw_pi { o with location }
  | Raw_lambda o -> Raw_lambda { o with location }
  | Raw_arrow o -> Raw_arrow { o with location }
  | Raw_annotated o -> Raw_annotated { o with location }
  | Raw_application o -> Raw_application { o with location }
  | Raw_block o -> Raw_block { o with location }
  | Raw_tuple o -> Raw_tuple { o with location }
  | Raw_projection o -> Raw_projection { o with location }
  | Raw_substitution o -> Raw_substitution { o with location }

let location_of_clf_context_object context_object =
  let open CLF.Context_object in
  let { location; _ } = context_object in
  location

(** {1 Meta-Level} *)

let location_of_meta_thing meta_thing =
  let open Meta.Thing in
  match meta_thing with
  | RawSchema { location; _ }
  | RawContext { location; _ }
  | RawTurnstile { location; _ } ->
      location

let location_of_schema_object schema_object =
  let open Meta.Schema_object in
  match schema_object with
  | Raw_constant { location; _ }
  | Raw_alternation { location; _ }
  | Raw_element { location; _ } ->
      location

let location_of_meta_context_object context_object =
  let open Meta.Context_object in
  let { location; _ } = context_object in
  location

(** {1 Computation-Level} *)

let location_of_comp_sort_object sort_object =
  let open Comp.Sort_object in
  match sort_object with
  | Raw_identifier { location; _ }
  | Raw_qualified_identifier { location; _ }
  | Raw_ctype { location; _ }
  | Raw_pi { location; _ }
  | Raw_arrow { location; _ }
  | Raw_cross { location; _ }
  | Raw_box { location; _ }
  | Raw_application { location; _ } ->
      location

let[@warning "-23"] set_location_of_comp_sort_object location sort_object =
  let open Comp.Sort_object in
  match sort_object with
  | Raw_identifier o -> Raw_identifier { o with location }
  | Raw_qualified_identifier o ->
      Raw_qualified_identifier { o with location }
  | Raw_ctype o -> Raw_ctype { o with location }
  | Raw_pi o -> Raw_pi { o with location }
  | Raw_arrow o -> Raw_arrow { o with location }
  | Raw_cross o -> Raw_cross { o with location }
  | Raw_box o -> Raw_box { o with location }
  | Raw_application o -> Raw_application { o with location }

let location_of_comp_expression_object expression_object =
  let open Comp.Expression_object in
  match expression_object with
  | Raw_identifier { location; _ }
  | Raw_qualified_identifier { location; _ }
  | Raw_fn { location; _ }
  | Raw_mlam { location; _ }
  | Raw_fun { location; _ }
  | Raw_box { location; _ }
  | Raw_let { location; _ }
  | Raw_impossible { location; _ }
  | Raw_case { location; _ }
  | Raw_tuple { location; _ }
  | Raw_hole { location; _ }
  | Raw_box_hole { location; _ }
  | Raw_application { location; _ }
  | Raw_annotated { location; _ }
  | Raw_observation { location; _ } ->
      location

let[@warning "-23"] set_location_of_comp_expression_object location
    expression_object =
  let open Comp.Expression_object in
  match expression_object with
  | Raw_identifier o -> Raw_identifier { o with location }
  | Raw_qualified_identifier o ->
      Raw_qualified_identifier { o with location }
  | Raw_fn o -> Raw_fn { o with location }
  | Raw_mlam o -> Raw_mlam { o with location }
  | Raw_fun o -> Raw_fun { o with location }
  | Raw_box o -> Raw_box { o with location }
  | Raw_let o -> Raw_let { o with location }
  | Raw_impossible o -> Raw_impossible { o with location }
  | Raw_case o -> Raw_case { o with location }
  | Raw_tuple o -> Raw_tuple { o with location }
  | Raw_hole o -> Raw_hole { o with location }
  | Raw_box_hole o -> Raw_box_hole { o with location }
  | Raw_application o -> Raw_application { o with location }
  | Raw_annotated o -> Raw_annotated { o with location }
  | Raw_observation o -> Raw_observation { o with location }

let location_of_comp_pattern_object pattern_object =
  let open Comp.Pattern_object in
  match pattern_object with
  | Raw_identifier { location; _ }
  | Raw_qualified_identifier { location; _ }
  | Raw_box { location; _ }
  | Raw_tuple { location; _ }
  | Raw_application { location; _ }
  | Raw_annotated { location; _ }
  | Raw_meta_annotated { location; _ }
  | Raw_wildcard { location; _ } ->
      location

let[@warning "-23"] set_location_of_comp_pattern_object location
    pattern_object =
  let open Comp.Pattern_object in
  match pattern_object with
  | Raw_identifier o -> Raw_identifier { o with location }
  | Raw_qualified_identifier o ->
      Raw_qualified_identifier { o with location }
  | Raw_box o -> Raw_box { o with location }
  | Raw_tuple o -> Raw_tuple { o with location }
  | Raw_application o -> Raw_application { o with location }
  | Raw_annotated o -> Raw_annotated { o with location }
  | Raw_meta_annotated o -> Raw_meta_annotated { o with location }
  | Raw_wildcard o -> Raw_wildcard { o with location }

let location_of_comp_copattern_object copattern_object =
  let open Comp.Copattern_object in
  match copattern_object with
  | Raw_observation { location; _ }
  | Raw_pattern { location; _ } ->
      location

let[@warning "-23"] set_location_of_comp_copattern_object location
    copattern_object =
  let open Comp.Copattern_object in
  match copattern_object with
  | Raw_observation o -> Raw_observation { o with location }
  | Raw_pattern o -> Raw_pattern { o with location }

let location_of_comp_context_object context_object =
  let open Comp.Context_object in
  let { location; _ } = context_object in
  location

(** {1 Harpoon} *)

let location_of_harpoon_proof proof =
  let open Harpoon.Proof in
  match proof with
  | Incomplete { location; _ }
  | Command { location; _ }
  | Directive { location; _ } ->
      location

let location_of_harpoon_command command =
  let open Harpoon.Command in
  match command with
  | By { location; _ }
  | Unbox { location; _ } ->
      location

let location_of_harpoon_directive directive =
  let open Harpoon.Directive in
  match directive with
  | Intros { location; _ }
  | Solve { location; _ }
  | Split { location; _ }
  | Impossible { location; _ }
  | Suffices { location; _ } ->
      location

let location_of_harpoon_split_branch split_branch =
  let open Harpoon.Split_branch in
  let { location; _ } = split_branch in
  location

let location_of_harpoon_split_branch_label split_branch_label =
  let open Harpoon.Split_branch.Label in
  match split_branch_label with
  | Constant { location; _ }
  | Bound_variable { location; _ }
  | Empty_context { location; _ }
  | Extended_context { location; _ }
  | Parameter_variable { location; _ } ->
      location

let location_of_harpoon_suffices_branch suffices_branch =
  let open Harpoon.Suffices_branch in
  let { location; _ } = suffices_branch in
  location

let location_of_harpoon_hypothetical hypothetical =
  let open Harpoon.Hypothetical in
  let { location; _ } = hypothetical in
  location

let location_of_harpoon_repl_command repl_command =
  let open Harpoon.Repl.Command in
  match repl_command with
  | Rename { location; _ }
  | Toggle_automation { location; _ }
  | Type { location; _ }
  | Info { location; _ }
  | Select_theorem { location; _ }
  | Theorem { location; _ }
  | Session { location; _ }
  | Subgoal { location; _ }
  | Undo { location; _ }
  | Redo { location; _ }
  | History { location; _ }
  | Translate { location; _ }
  | Intros { location; _ }
  | Split { location; _ }
  | Invert { location; _ }
  | Impossible { location; _ }
  | Msplit { location; _ }
  | Solve { location; _ }
  | Unbox { location; _ }
  | By { location; _ }
  | Suffices { location; _ }
  | Help { location; _ } ->
      location

(** {1 Signature} *)

let location_of_signature_pragma pragma =
  let open Signature.Pragma in
  match pragma with
  | Name { location; _ }
  | Default_associativity { location; _ }
  | Prefix_fixity { location; _ }
  | Infix_fixity { location; _ }
  | Postfix_fixity { location; _ }
  | Not { location; _ }
  | Open_module { location; _ }
  | Abbreviation { location; _ } ->
      location

let location_of_signature_global_pragma global_pragma =
  let open Signature.Global_pragma in
  match global_pragma with
  | No_strengthening { location; _ }
  | Warn_on_coverage_error { location; _ }
  | Raise_error_on_coverage_error { location; _ } ->
      location

let location_of_signature_totality_declaration totality_declaration =
  let open Signature.Totality.Declaration in
  match totality_declaration with
  | Trust { location; _ }
  | Numeric { location; _ }
  | Named { location; _ } ->
      location

let location_of_signature_totality_order totality_order =
  let open Signature.Totality.Order in
  match totality_order with
  | Argument { location; _ }
  | Lexical_ordering { location; _ }
  | Simultaneous_ordering { location; _ } ->
      location

let location_of_signature_entry entry =
  let open Signature.Entry in
  match entry with
  | Raw_declaration { location; _ }
  | Raw_pragma { location; _ }
  | Raw_comment { location; _ } ->
      location

let location_of_signature_declaration declaration =
  let open Signature.Declaration in
  match declaration with
  | Raw_lf_typ_or_term_constant { location; _ }
  | Raw_lf_typ_constant { location; _ }
  | Raw_lf_term_constant { location; _ }
  | Raw_inductive_comp_typ_constant { location; _ }
  | Raw_stratified_comp_typ_constant { location; _ }
  | Raw_comp_cotyp_constant { location; _ }
  | Raw_comp_expression_constructor { location; _ }
  | Raw_comp_expression_destructor { location; _ }
  | Raw_comp_typ_abbreviation { location; _ }
  | Raw_schema { location; _ }
  | Raw_theorem { location; _ }
  | Raw_proof { location; _ }
  | Raw_recursive_declarations { location; _ }
  | Raw_val { location; _ }
  | Raw_query { location; _ }
  | Raw_module { location; _ } ->
      location
