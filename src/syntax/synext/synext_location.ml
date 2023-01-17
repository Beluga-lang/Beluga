open Synext_definition

(** {1 LF} *)

let location_of_lf_kind kind =
  let open LF.Kind in
  match kind with
  | Typ { location; _ }
  | Arrow { location; _ }
  | Pi { location; _ } ->
      location

let location_of_lf_typ typ =
  let open LF.Typ in
  match typ with
  | Constant { location; _ }
  | Application { location; _ }
  | Arrow { location; _ }
  | Pi { location; _ } ->
      location

let location_of_lf_term term =
  let open LF.Term in
  match term with
  | Variable { location; _ }
  | Constant { location; _ }
  | Application { location; _ }
  | Abstraction { location; _ }
  | Wildcard { location; _ }
  | Type_annotated { location; _ } ->
      location

(** {1 Contextual LF} *)

let location_of_clf_typ typ =
  let open CLF.Typ in
  match typ with
  | Constant { location; _ }
  | Application { location; _ }
  | Arrow { location; _ }
  | Pi { location; _ }
  | Block { location; _ } ->
      location

let location_of_clf_term term =
  let open CLF.Term in
  match term with
  | Variable { location; _ }
  | Parameter_variable { location; _ }
  | Substitution_variable { location; _ }
  | Constant { location; _ }
  | Application { location; _ }
  | Abstraction { location; _ }
  | Hole { location; _ }
  | Substitution { location; _ }
  | Tuple { location; _ }
  | Projection { location; _ }
  | Type_annotated { location; _ } ->
      location

let location_of_clf_substitution substitution =
  let open CLF.Substitution in
  let { location; _ } = substitution in
  location

let location_of_clf_substitution_pattern substitution_pattern =
  let open CLF.Substitution.Pattern in
  let { location; _ } = substitution_pattern in
  location

let location_of_clf_context context =
  let open CLF.Context in
  let { location; _ } = context in
  location

let location_of_clf_context_pattern context_pattern =
  let open CLF.Context.Pattern in
  let { location; _ } = context_pattern in
  location

let location_of_clf_term_pattern term_pattern =
  let open CLF.Term.Pattern in
  match term_pattern with
  | Variable { location; _ }
  | Parameter_variable { location; _ }
  | Substitution_variable { location; _ }
  | Constant { location; _ }
  | Wildcard { location; _ }
  | Tuple { location; _ }
  | Projection { location; _ }
  | Abstraction { location; _ }
  | Substitution { location; _ }
  | Application { location; _ }
  | Type_annotated { location; _ } ->
      location

(** {1 Meta-Level} *)

let location_of_meta_type meta_type =
  let open Meta.Typ in
  match meta_type with
  | Context_schema { location; _ }
  | Contextual_typ { location; _ }
  | Parameter_typ { location; _ }
  | Plain_substitution_typ { location; _ }
  | Renaming_substitution_typ { location; _ } ->
      location

let location_of_meta_object meta_object =
  let open Meta.Object in
  match meta_object with
  | Context { location; _ }
  | Contextual_term { location; _ }
  | Plain_substitution { location; _ }
  | Renaming_substitution { location; _ } ->
      location

let location_of_meta_object_pattern meta_object_pattern =
  let open Meta.Pattern in
  match meta_object_pattern with
  | Context { location; _ }
  | Contextual_term { location; _ }
  | Plain_substitution { location; _ }
  | Renaming_substitution { location; _ } ->
      location

let location_of_meta_context context =
  let open Meta.Context in
  let { location; _ } = context in
  location

let location_of_schema schema =
  let open Meta.Schema in
  match schema with
  | Constant { location; _ }
  | Alternation { location; _ }
  | Element { location; _ } ->
      location

(** {1 Computation-Level} *)

let location_of_comp_kind kind =
  let open Comp.Kind in
  match kind with
  | Pi { location; _ }
  | Arrow { location; _ }
  | Ctype { location; _ } ->
      location

let location_of_comp_typ typ =
  let open Comp.Typ in
  match typ with
  | Constant { location; _ }
  | Pi { location; _ }
  | Arrow { location; _ }
  | Cross { location; _ }
  | Box { location; _ }
  | Application { location; _ } ->
      location

let location_of_comp_expression expression =
  let open Comp.Expression in
  match expression with
  | Fn { location; _ }
  | Fun { location; _ }
  | Mlam { location; _ }
  | Let { location; _ }
  | Box { location; _ }
  | Impossible { location; _ }
  | Case { location; _ }
  | Tuple { location; _ }
  | Hole { location; _ }
  | BoxHole { location; _ }
  | Variable { location; _ }
  | Constant { location; _ }
  | Application { location; _ }
  | Observation { location; _ }
  | Type_annotated { location; _ } ->
      location

let location_of_comp_pattern pattern =
  let open Comp.Pattern in
  match pattern with
  | Variable { location; _ }
  | Constant { location; _ }
  | MetaObject { location; _ }
  | Tuple { location; _ }
  | Application { location; _ }
  | Type_annotated { location; _ }
  | MetaTypeAnnotated { location; _ }
  | Wildcard { location; _ } ->
      location

let location_of_comp_copattern copattern =
  let open Comp.Copattern in
  match copattern with
  | Pattern pattern -> location_of_comp_pattern pattern
  | Observation { location; _ } -> location

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
  | Pragma { location; _ }
  | Declaration { location; _ }
  | Comment { location; _ } ->
      location

let location_of_signature_declaration declaration =
  let open Signature.Declaration in
  match declaration with
  | Typ { location; _ }
  | Const { location; _ }
  | CompTyp { location; _ }
  | CompCotyp { location; _ }
  | CompConst { location; _ }
  | CompDest { location; _ }
  | CompTypAbbrev { location; _ }
  | Schema { location; _ }
  | Theorem { location; _ }
  | Proof { location; _ }
  | Recursive_declarations { location; _ }
  | Val { location; _ }
  | Query { location; _ }
  | MQuery { location; _ }
  | Module { location; _ } ->
      location
