(** Equality predicates on the external syntax, without locations.

    This is used to assert the equality between external syntax objects. *)

open Support
open Beluga
open Synext'

module LF = struct
  open LF

  let rec kind_equal x y =
    match (x, y) with
    | Kind.Typ _, Kind.Typ _ -> true
    | Kind.Arrow x, Kind.Arrow y ->
      typ_equal x.domain y.domain && kind_equal x.range y.range
    | Kind.Pi x, Kind.Pi y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && typ_equal x.parameter_type y.parameter_type
      && kind_equal x.body y.body
    | _ -> false

  and typ_equal x y =
    match (x, y) with
    | Typ.Constant x, Typ.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Typ.Application x, Typ.Application y ->
      typ_equal x.applicand y.applicand
      && List.equal term_equal x.arguments y.arguments
    | Typ.Arrow x, Typ.Arrow y ->
      x.orientation = y.orientation
      && typ_equal x.domain y.domain
      && typ_equal x.range y.range
    | Typ.Pi x, Typ.Pi y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && typ_equal x.parameter_type y.parameter_type
      && typ_equal x.body y.body
    | _ -> false

  and term_equal x y =
    match (x, y) with
    | Term.Variable x, Term.Variable y ->
      Identifier.equal x.identifier y.identifier
    | Term.Constant x, Term.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Term.Application x, Term.Application y ->
      term_equal x.applicand y.applicand
      && List.equal term_equal x.arguments y.arguments
    | Term.Abstraction x, Term.Abstraction y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && Option.equal typ_equal x.parameter_type y.parameter_type
      && term_equal x.body y.body
    | Term.Wildcard _, Term.Wildcard _ -> true
    | Term.TypeAnnotated x, Term.TypeAnnotated y ->
      term_equal x.term y.term && typ_equal x.typ y.typ
    | _ -> false
end

module CLF = struct
  open CLF

  let rec typ_equal x y =
    match (x, y) with
    | Typ.Constant x, Typ.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Typ.Application x, Typ.Application y ->
      typ_equal x.applicand y.applicand
      && List.equal term_equal x.arguments y.arguments
    | Typ.Arrow x, Typ.Arrow y ->
      x.orientation = y.orientation
      && typ_equal x.domain y.domain
      && typ_equal x.range y.range
    | Typ.Pi x, Typ.Pi y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && typ_equal x.parameter_type y.parameter_type
      && typ_equal x.body y.body
    | ( Typ.Block { elements = `Unnamed t1; _ }
      , Typ.Block { elements = `Unnamed t2; _ } ) -> typ_equal t1 t2
    | ( Typ.Block { elements = `Record ts1; _ }
      , Typ.Block { elements = `Record ts2; _ } ) ->
      List1.equal (Pair.equal Identifier.equal typ_equal) ts1 ts2
    | _ -> false

  and term_equal x y =
    match (x, y) with
    | Term.Variable x, Term.Variable y ->
      Identifier.equal x.identifier y.identifier
    | Term.Constant x, Term.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Term.Application x, Term.Application y ->
      term_equal x.applicand y.applicand
      && List.equal term_equal x.arguments y.arguments
    | Term.Substitution x, Term.Substitution y ->
      term_equal x.term y.term
      && substitution_equal x.substitution y.substitution
    | Term.Abstraction x, Term.Abstraction y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && Option.equal typ_equal x.parameter_type y.parameter_type
      && term_equal x.body y.body
    | ( Term.Hole { variant = `Underscore; _ }
      , Term.Hole { variant = `Underscore; _ } ) -> true
    | ( Term.Hole { variant = `Unlabelled; _ }
      , Term.Hole { variant = `Unlabelled; _ } ) -> true
    | ( Term.Hole { variant = `Labelled l1; _ }
      , Term.Hole { variant = `Labelled l2; _ } ) -> Identifier.equal l1 l2
    | Term.Tuple x, Term.Tuple y -> List1.equal term_equal x.terms y.terms
    | Term.Projection x, Term.Projection y -> (
      term_equal x.term y.term
      &&
      match (x.projection, y.projection) with
      | `By_identifier i1, `By_identifier i2 -> Identifier.equal i1 i2
      | `By_position i1, `By_position i2 -> Int.equal i1 i2
      | _ -> false)
    | Term.TypeAnnotated x, Term.TypeAnnotated y ->
      term_equal x.term y.term && typ_equal x.typ y.typ
    | _ -> false

  and term_pattern_equal x y =
    match (x, y) with
    | Term.Pattern.Variable x, Term.Pattern.Variable y ->
      Identifier.equal x.identifier y.identifier
    | Term.Pattern.Constant x, Term.Pattern.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Term.Pattern.Application x, Term.Pattern.Application y ->
      term_pattern_equal x.applicand y.applicand
      && List.equal term_pattern_equal x.arguments y.arguments
    | Term.Pattern.Substitution x, Term.Pattern.Substitution y ->
      term_pattern_equal x.term y.term
      && substitution_equal x.substitution y.substitution
    | Term.Pattern.Abstraction x, Term.Pattern.Abstraction y ->
      Option.equal Identifier.equal x.parameter_identifier
        y.parameter_identifier
      && Option.equal typ_equal x.parameter_type y.parameter_type
      && term_pattern_equal x.body y.body
    | Term.Pattern.Wildcard _, Term.Pattern.Wildcard _ -> true
    | Term.Pattern.Tuple x, Term.Pattern.Tuple y ->
      List1.equal term_pattern_equal x.terms y.terms
    | Term.Pattern.Projection x, Term.Pattern.Projection y -> (
      term_pattern_equal x.term y.term
      &&
      match (x.projection, y.projection) with
      | `By_identifier i1, `By_identifier i2 -> Identifier.equal i1 i2
      | `By_position i1, `By_position i2 -> Int.equal i1 i2
      | _ -> false)
    | Term.Pattern.TypeAnnotated x, Term.Pattern.TypeAnnotated y ->
      term_pattern_equal x.term y.term && typ_equal x.typ y.typ
    | _ -> false

  and substitution_equal x y =
    let open Substitution in
    substitution_head_equal x.head y.head
    && List.equal term_equal x.terms y.terms

  and substitution_head_equal x y =
    match (x, y) with
    | Substitution.Head.None _, Substitution.Head.None _
    | Substitution.Head.Identity _, Substitution.Head.Identity _ -> true
    | ( Substitution.Head.Substitution_variable x
      , Substitution.Head.Substitution_variable y ) ->
      Identifier.equal x.identifier y.identifier
      && Option.equal substitution_equal x.closure y.closure
    | _ -> false

  and substitution_pattern_equal x y =
    let open Substitution.Pattern in
    substitution_pattern_head_equal x.head y.head
    && List.equal term_pattern_equal x.terms y.terms

  and substitution_pattern_head_equal x y =
    match (x, y) with
    | Substitution.Pattern.Head.None _, Substitution.Pattern.Head.None _
    | ( Substitution.Pattern.Head.Identity _
      , Substitution.Pattern.Head.Identity _ ) -> true
    | ( Substitution.Pattern.Head.Substitution_variable
          { identifier = i1; closure = o1; _ }
      , Substitution.Pattern.Head.Substitution_variable
          { identifier = i2; closure = o2; _ } ) ->
      Identifier.equal i1 i2 && Option.equal substitution_equal o1 o2
    | _ -> false

  and context_equal x y =
    let open Context in
    context_head_equal x.head y.head
    && List.equal
         (Pair.equal Identifier.equal (Option.equal typ_equal))
         x.bindings y.bindings

  and context_head_equal x y =
    match (x, y) with
    | Context.Head.None _, Context.Head.None _
    | Context.Head.Hole _, Context.Head.Hole _ -> true
    | Context.Head.Context_variable x, Context.Head.Context_variable y ->
      Identifier.equal x.identifier y.identifier
    | _ -> false

  and context_pattern_equal x y =
    let open Context.Pattern in
    context_pattern_head_equal x.head y.head
    && List.equal
         (Pair.equal Identifier.equal typ_equal)
         x.bindings y.bindings

  and context_pattern_head_equal x y =
    match (x, y) with
    | Context.Pattern.Head.None _, Context.Pattern.Head.None _
    | Context.Pattern.Head.Hole _, Context.Pattern.Head.Hole _ -> true
    | ( Context.Pattern.Head.Context_variable x
      , Context.Pattern.Head.Context_variable y ) ->
      Identifier.equal x.identifier y.identifier
    | _ -> false
end

module Meta = struct
  open Meta

  let rec typ_equal x y =
    match (x, y) with
    | Typ.Context_schema x, Typ.Context_schema y ->
      schema_equal x.schema y.schema
    | Typ.Contextual_typ x, Typ.Contextual_typ y ->
      CLF.context_equal x.context y.context && CLF.typ_equal x.typ y.typ
    | Typ.Parameter_typ x, Typ.Parameter_typ y ->
      CLF.context_equal x.context y.context && CLF.typ_equal x.typ y.typ
    | Typ.Plain_substitution_typ x, Typ.Plain_substitution_typ y ->
      CLF.context_equal x.domain y.domain
      && CLF.context_equal x.range y.range
    | Typ.Renaming_substitution_typ x, Typ.Renaming_substitution_typ y ->
      CLF.context_equal x.domain y.domain
      && CLF.context_equal x.range y.range
    | _ -> false

  and object_equal x y =
    match (x, y) with
    | Object.Context x, Object.Context y ->
      CLF.context_equal x.context y.context
    | Object.Contextual_term x, Object.Contextual_term y ->
      CLF.context_equal x.context y.context && CLF.term_equal x.term y.term
    | Object.Plain_substitution x, Object.Plain_substitution y ->
      CLF.context_equal x.domain y.domain
      && CLF.substitution_equal x.range y.range
    | Object.Renaming_substitution x, Object.Renaming_substitution y ->
      CLF.context_equal x.domain y.domain
      && CLF.substitution_equal x.range y.range
    | _ -> false

  and pattern_equal x y =
    match (x, y) with
    | Pattern.Context x, Pattern.Context y ->
      CLF.context_pattern_equal x.context y.context
    | Pattern.Contextual_term x, Pattern.Contextual_term y ->
      CLF.context_pattern_equal x.context y.context
      && CLF.term_pattern_equal x.term y.term
    | Pattern.Plain_substitution x, Pattern.Plain_substitution y ->
      CLF.context_pattern_equal x.domain y.domain
      && CLF.substitution_pattern_equal x.range y.range
    | Pattern.Renaming_substitution x, Pattern.Renaming_substitution y ->
      CLF.context_pattern_equal x.domain y.domain
      && CLF.substitution_pattern_equal x.range y.range
    | _ -> false

  and substitution_equal x y =
    let open Substitution in
    List.equal object_equal x.objects y.objects

  and context_equal x y =
    let open Context in
    List.equal (Pair.equal Identifier.equal typ_equal) x.bindings y.bindings

  and schema_equal x y =
    match (x, y) with
    | Schema.Constant x, Schema.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
    | Schema.Alternation x, Schema.Alternation y ->
      List2.equal schema_equal x.schemas y.schemas
    | ( Schema.Element { some = s1; block = `Unnamed b1; _ }
      , Schema.Element { some = s2; block = `Unnamed b2; _ } ) ->
      Option.equal
        (List1.equal (Pair.equal Identifier.equal CLF.typ_equal))
        s1 s2
      && CLF.typ_equal b1 b2
    | ( Schema.Element { some = s1; block = `Record b1; _ }
      , Schema.Element { some = s2; block = `Record b2; _ } ) ->
      Option.equal
        (List1.equal (Pair.equal Identifier.equal CLF.typ_equal))
        s1 s2
      && List1.equal (Pair.equal Identifier.equal CLF.typ_equal) b1 b2
    | _ -> false
end

module Comp = struct
  open Comp

  let rec kind_equal x y =
    match (x, y) with
    | Kind.Ctype _, Kind.Ctype _ -> true
    | Kind.Arrow x, Kind.Arrow y ->
      typ_equal x.domain y.domain && kind_equal x.range y.range
    | Kind.Pi x, Kind.Pi y ->
      Plicity.equal x.plicity y.plicity
      && Option.equal Identifier.equal x.parameter_identifier
           y.parameter_identifier
      && Meta.typ_equal x.parameter_type y.parameter_type
      && kind_equal x.body y.body
    | _ -> false

  and typ_equal x y =
    match (x, y) with
    | Typ.Constant x, Typ.Constant y ->
      Bool.equal x.quoted y.quoted
      && QualifiedIdentifier.equal x.identifier y.identifier
    | Typ.Pi x, Typ.Pi y ->
      Plicity.equal x.plicity y.plicity
      && Option.equal Identifier.equal x.parameter_identifier
           y.parameter_identifier
      && Meta.typ_equal x.parameter_type y.parameter_type
      && typ_equal x.body y.body
    | Typ.Arrow x, Typ.Arrow y ->
      typ_equal x.domain y.domain && typ_equal x.range y.range
    | Typ.Cross x, Typ.Cross y -> List2.equal typ_equal x.types y.types
    | Typ.Box x, Typ.Box y -> Meta.typ_equal x.meta_type y.meta_type
    | Typ.Application x, Typ.Application y ->
      typ_equal x.applicand y.applicand
      && List1.equal typ_equal x.arguments y.arguments
    | Typ.Base x, Typ.Base y ->
      QualifiedIdentifier.equal x.applicand y.applicand
      && List.equal Meta.object_equal x.arguments y.arguments
    | Typ.Cobase x, Typ.Cobase y ->
      QualifiedIdentifier.equal x.applicand y.applicand
      && List.equal Meta.object_equal x.arguments y.arguments
    | _ -> false

  and expression_equal x y =
    match (x, y) with
    | Expression.Variable x, Expression.Variable y ->
      Identifier.equal x.identifier y.identifier
    | Expression.Constant x, Expression.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
      && Bool.equal x.quoted y.quoted
    | Expression.Fn x, Expression.Fn y ->
      List1.equal (Option.equal Identifier.equal) x.parameters y.parameters
      && expression_equal x.body y.body
    | Expression.Mlam x, Expression.Mlam y ->
      List1.equal
        (fun (ix, mx) (iy, my) ->
          Option.equal Identifier.equal ix iy && mx = my)
        x.parameters y.parameters
      && expression_equal x.body y.body
    | Expression.Fun x, Expression.Fun y ->
      List1.equal
        (fun (px, ex) (py, ey) ->
          List1.equal pattern_equal px py && expression_equal ex ey)
        x.branches y.branches
    | Expression.Let x, Expression.Let y ->
      pattern_equal x.pattern y.pattern
      && expression_equal x.scrutinee y.scrutinee
      && expression_equal x.body y.body
    | Expression.Box x, Expression.Box y ->
      Meta.object_equal x.meta_object y.meta_object
    | Expression.Impossible x, Expression.Impossible y ->
      expression_equal x.scrutinee y.scrutinee
    | Expression.Case x, Expression.Case y ->
      Bool.equal x.check_coverage y.check_coverage
      && expression_equal x.scrutinee y.scrutinee
      && List1.equal
           (fun (px, ex) (py, ey) ->
             pattern_equal px py && expression_equal ex ey)
           x.branches y.branches
    | Expression.Tuple x, Expression.Tuple y ->
      List2.equal expression_equal x.elements y.elements
    | Expression.Hole x, Expression.Hole y ->
      Option.equal Identifier.equal x.label y.label
    | Expression.BoxHole _, Expression.BoxHole _ -> true
    | Expression.Application x, Expression.Application y ->
      expression_equal x.applicand y.applicand
      && List1.equal expression_equal x.arguments y.arguments
    | Expression.Observation x, Expression.Observation y ->
      QualifiedIdentifier.equal x.observation y.observation
      && List.equal expression_equal x.arguments y.arguments
    | Expression.TypeAnnotated x, Expression.TypeAnnotated y ->
      expression_equal x.expression y.expression && typ_equal x.typ y.typ
    | _ -> false

  and pattern_equal x y =
    match (x, y) with
    | Pattern.Variable x, Pattern.Variable y ->
      Identifier.equal x.identifier y.identifier
    | Pattern.Constant x, Pattern.Constant y ->
      Bool.equal x.quoted y.quoted
      && QualifiedIdentifier.equal x.identifier y.identifier
    | Pattern.MetaObject x, Pattern.MetaObject y ->
      Meta.pattern_equal x.meta_pattern y.meta_pattern
    | Pattern.Tuple x, Pattern.Tuple y ->
      List2.equal pattern_equal x.elements y.elements
    | Pattern.Application x, Pattern.Application y ->
      pattern_equal x.applicand y.applicand
      && List1.equal pattern_equal x.arguments y.arguments
    | Pattern.Observation x, Pattern.Observation y ->
      QualifiedIdentifier.equal x.observation y.observation
      && List.equal pattern_equal x.arguments y.arguments
    | Pattern.TypeAnnotated x, Pattern.TypeAnnotated y ->
      pattern_equal x.pattern y.pattern && typ_equal x.typ y.typ
    | Pattern.MetaTypeAnnotated x, Pattern.MetaTypeAnnotated y ->
      Option.equal Identifier.equal x.annotation_identifier
        y.annotation_identifier
      && Meta.typ_equal x.annotation_type y.annotation_type
      && pattern_equal x.body y.body
    | Pattern.Wildcard _, Pattern.Wildcard _ -> true
    | _ -> false

  and context_equal x y =
    let open Context in
    List.equal
      (fun (ix, tx) (iy, ty) -> Identifier.equal ix iy && typ_equal tx ty)
      x.bindings y.bindings
end

module Harpoon = struct
  open Harpoon

  let rec proof_equal x y =
    match (x, y) with
    | Proof.Incomplete x, Proof.Incomplete y ->
      Option.equal Identifier.equal x.label y.label
    | Proof.Command x, Proof.Command y ->
      command_equal x.command y.command && proof_equal x.body y.body
    | Proof.Directive x, Proof.Directive y ->
      directive_equal x.directive y.directive
    | _ -> false

  and command_equal x y =
    match (x, y) with
    | Command.By x, Command.By y ->
      Identifier.equal x.assignee y.assignee
      && Comp.expression_equal x.expression y.expression
    | Command.Unbox x, Command.Unbox y ->
      Identifier.equal x.assignee y.assignee
      && x.modifier = y.modifier
      && Comp.expression_equal x.expression y.expression
    | _ -> false

  and directive_equal x y =
    match (x, y) with
    | Directive.Intros x, Directive.Intros y ->
      hypothetical_equal x.hypothetical y.hypothetical
    | Directive.Solve x, Directive.Solve y ->
      Comp.expression_equal x.solution y.solution
    | Directive.Split x, Directive.Split y ->
      Comp.expression_equal x.scrutinee y.scrutinee
      && List.equal split_branch_equal x.branches y.branches
    | Directive.Suffices x, Directive.Suffices y ->
      Comp.expression_equal x.scrutinee y.scrutinee
      && List.equal suffices_branch_equal x.branches y.branches
    | _ -> false

  and split_branch_equal x y =
    let open Split_branch in
    split_branch_label_equal x.label y.label
    && hypothetical_equal x.body y.body

  and split_branch_label_equal x y =
    match (x, y) with
    | Split_branch.Label.Constant x, Split_branch.Label.Constant y ->
      QualifiedIdentifier.equal x.identifier y.identifier
    | ( Split_branch.Label.Bound_variable _
      , Split_branch.Label.Bound_variable _ ) -> true
    | Split_branch.Label.Empty_context _, Split_branch.Label.Empty_context _
      -> true
    | ( Split_branch.Label.Extended_context x
      , Split_branch.Label.Extended_context y ) ->
      Int.equal x.schema_element y.schema_element
    | ( Split_branch.Label.Parameter_variable x
      , Split_branch.Label.Parameter_variable y ) ->
      Int.equal x.schema_element y.schema_element
      && Option.equal Int.equal x.projection y.projection
    | _ -> false

  and suffices_branch_equal x y =
    let open Suffices_branch in
    Comp.typ_equal x.goal y.goal && proof_equal x.proof y.proof

  and hypothetical_equal x y =
    let open Hypothetical in
    Meta.context_equal x.meta_context y.meta_context
    && Comp.context_equal x.comp_context y.comp_context
    && proof_equal x.proof y.proof

  and repl_command_equal x y =
    match (x, y) with
    | Repl.Command.Rename x, Repl.Command.Rename y ->
      Identifier.equal x.rename_from y.rename_from
      && Identifier.equal x.rename_to y.rename_to
      && x.level = y.level
    | Repl.Command.ToggleAutomation x, Repl.Command.ToggleAutomation y ->
      x.kind = y.kind && x.change = y.change
    | Repl.Command.Type x, Repl.Command.Type y ->
      Comp.expression_equal x.scrutinee y.scrutinee
    | Repl.Command.Info x, Repl.Command.Info y ->
      x.kind = y.kind
      && QualifiedIdentifier.equal x.object_identifier y.object_identifier
    | Repl.Command.SelectTheorem x, Repl.Command.SelectTheorem y ->
      QualifiedIdentifier.equal x.theorem y.theorem
    | Repl.Command.Theorem x, Repl.Command.Theorem y ->
      x.subcommand = y.subcommand
    | Repl.Command.Session x, Repl.Command.Session y ->
      x.subcommand = y.subcommand
    | Repl.Command.Subgoal x, Repl.Command.Subgoal y ->
      x.subcommand = y.subcommand
    | Repl.Command.Undo _, Repl.Command.Undo _ -> true
    | Repl.Command.Redo _, Repl.Command.Redo _ -> true
    | Repl.Command.History _, Repl.Command.History _ -> true
    | Repl.Command.Translate x, Repl.Command.Translate y ->
      QualifiedIdentifier.equal x.theorem y.theorem
    | Repl.Command.Intros x, Repl.Command.Intros y ->
      Option.equal
        (List1.equal Identifier.equal)
        x.introduced_variables y.introduced_variables
    | Repl.Command.Split x, Repl.Command.Split y ->
      Comp.expression_equal x.scrutinee y.scrutinee
    | Repl.Command.Invert x, Repl.Command.Invert y ->
      Comp.expression_equal x.scrutinee y.scrutinee
    | Repl.Command.Impossible x, Repl.Command.Impossible y ->
      Comp.expression_equal x.scrutinee y.scrutinee
    | Repl.Command.MSplit x, Repl.Command.MSplit y ->
      Identifier.equal x.identifier y.identifier
    | Repl.Command.Solve x, Repl.Command.Solve y ->
      Comp.expression_equal x.solution y.solution
    | Repl.Command.Unbox x, Repl.Command.Unbox y ->
      x.modifier = y.modifier
      && Identifier.equal x.assignee y.assignee
      && Comp.expression_equal x.expression y.expression
    | Repl.Command.By x, Repl.Command.By y ->
      Identifier.equal x.assignee y.assignee
      && Comp.expression_equal x.expression y.expression
    | Repl.Command.Suffices x, Repl.Command.Suffices y ->
      Comp.expression_equal x.implication y.implication
      && List.equal
           (fun x y ->
             match (x, y) with
             | `exact x, `exact y -> Comp.typ_equal x y
             | `infer _, `infer _ -> true
             | _ -> false)
           x.goal_premises y.goal_premises
    | Repl.Command.Help _, Repl.Command.Help _ -> true
    | _ -> false
end

module Signature = struct
  open Signature

  let rec pragma_equal x y =
    match (x, y) with
    | Pragma.Name x, Pragma.Name y ->
      QualifiedIdentifier.equal x.constant y.constant
      && Identifier.equal x.meta_variable_base y.meta_variable_base
      && Option.equal Identifier.equal x.computation_variable_base
           y.computation_variable_base
    | Pragma.Default_associativity x, Pragma.Default_associativity y ->
      Associativity.equal x.associativity y.associativity
    | Pragma.Prefix_fixity x, Pragma.Prefix_fixity y ->
      QualifiedIdentifier.equal x.constant y.constant
      && Int.equal x.precedence y.precedence
    | Pragma.Infix_fixity x, Pragma.Infix_fixity y ->
      QualifiedIdentifier.equal x.constant y.constant
      && Int.equal x.precedence y.precedence
      && Option.equal Associativity.equal x.associativity y.associativity
    | Pragma.Postfix_fixity x, Pragma.Postfix_fixity y ->
      QualifiedIdentifier.equal x.constant y.constant
      && Int.equal x.precedence y.precedence
    | Pragma.Not _, Pragma.Not _ -> true
    | Pragma.Open_module x, Pragma.Open_module y ->
      QualifiedIdentifier.equal x.module_identifier y.module_identifier
    | Pragma.Abbreviation x, Pragma.Abbreviation y ->
      QualifiedIdentifier.equal x.module_identifier y.module_identifier
      && Identifier.equal x.abbreviation y.abbreviation
    | _ -> false

  and global_pragma_equal x y =
    match (x, y) with
    | Pragma.Global.No_strengthening _, Pragma.Global.No_strengthening _ ->
      true
    | Pragma.Global.Coverage x, Pragma.Global.Coverage y ->
      x.variant = y.variant
    | _ -> false

  and totality_declaration_equal x y =
    match (x, y) with
    | Totality.Declaration.Trust _, Totality.Declaration.Trust _ -> true
    | Totality.Declaration.Numeric x, Totality.Declaration.Numeric y ->
      Option.equal numeric_totality_order_equal x.order y.order
    | Totality.Declaration.Named x, Totality.Declaration.Named y ->
      Option.equal named_totality_order_equal x.order y.order
    | _ -> false

  and named_totality_order_equal x y =
    match (x, y) with
    | Totality.Order.Argument x, Totality.Order.Argument y ->
      Identifier.equal x.argument y.argument
    | Totality.Order.Lexical_ordering x, Totality.Order.Lexical_ordering y ->
      List1.equal named_totality_order_equal x.arguments y.arguments
    | ( Totality.Order.Simultaneous_ordering x
      , Totality.Order.Simultaneous_ordering y ) ->
      List1.equal named_totality_order_equal x.arguments y.arguments
    | _ -> false

  and numeric_totality_order_equal x y =
    match (x, y) with
    | Totality.Order.Argument x, Totality.Order.Argument y ->
      Int.equal x.argument y.argument
    | Totality.Order.Lexical_ordering x, Totality.Order.Lexical_ordering y ->
      List1.equal numeric_totality_order_equal x.arguments y.arguments
    | ( Totality.Order.Simultaneous_ordering x
      , Totality.Order.Simultaneous_ordering y ) ->
      List1.equal numeric_totality_order_equal x.arguments y.arguments
    | _ -> false

  and declaration_equal x y =
    match (x, y) with
    | Declaration.Typ x, Declaration.Typ y ->
      Identifier.equal x.identifier y.identifier
      && LF.kind_equal x.kind y.kind
    | Declaration.Const x, Declaration.Const y ->
      Identifier.equal x.identifier y.identifier && LF.typ_equal x.typ y.typ
    | Declaration.CompTyp x, Declaration.CompTyp y ->
      x.datatype_flavour = y.datatype_flavour
      && Identifier.equal x.identifier y.identifier
      && Comp.kind_equal x.kind y.kind
    | Declaration.CompCotyp x, Declaration.CompCotyp y ->
      Identifier.equal x.identifier y.identifier
      && Comp.kind_equal x.kind y.kind
    | Declaration.CompConst x, Declaration.CompConst y ->
      Identifier.equal x.identifier y.identifier
      && Comp.typ_equal x.typ y.typ
    | Declaration.CompDest x, Declaration.CompDest y ->
      Identifier.equal x.identifier y.identifier
      && Comp.typ_equal x.observation_type y.observation_type
      && Comp.typ_equal x.return_type y.return_type
    | Declaration.CompTypAbbrev x, Declaration.CompTypAbbrev y ->
      Identifier.equal x.identifier y.identifier
      && Comp.kind_equal x.kind y.kind
      && Comp.typ_equal x.typ y.typ
    | Declaration.Schema x, Declaration.Schema y ->
      Identifier.equal x.identifier y.identifier
      && Meta.schema_equal x.schema y.schema
    | Declaration.Pragma x, Declaration.Pragma y ->
      pragma_equal x.pragma y.pragma
    | Declaration.GlobalPragma x, Declaration.GlobalPragma y ->
      global_pragma_equal x.pragma y.pragma
    | Declaration.Theorem x, Declaration.Theorem y ->
      Identifier.equal x.name y.name
      && Comp.typ_equal x.typ y.typ
      && Option.equal totality_declaration_equal x.order y.order
      && Comp.expression_equal x.body y.body
    | Declaration.Proof x, Declaration.Proof y ->
      Identifier.equal x.name y.name
      && Comp.typ_equal x.typ y.typ
      && Option.equal totality_declaration_equal x.order y.order
      && Harpoon.proof_equal x.body y.body
    | ( Declaration.Recursive_declarations x
      , Declaration.Recursive_declarations y ) ->
      List1.equal declaration_equal x.declarations y.declarations
    | Declaration.Val x, Declaration.Val y ->
      Identifier.equal x.identifier y.identifier
      && Option.equal Comp.typ_equal x.typ y.typ
      && Comp.expression_equal x.expression y.expression
    | Declaration.Query x, Declaration.Query y ->
      Option.equal Identifier.equal x.name y.name
      && Meta.context_equal x.meta_context y.meta_context
      && LF.typ_equal x.typ y.typ
      && Option.equal Int.equal x.expected_solutions y.expected_solutions
      && Option.equal Int.equal x.maximum_tries y.maximum_tries
    | Declaration.MQuery x, Declaration.MQuery y ->
      Comp.typ_equal x.typ y.typ
      && Option.equal Int.equal x.expected_solutions y.expected_solutions
      && Option.equal Int.equal x.search_tries y.search_tries
      && Option.equal Int.equal x.search_depth y.search_depth
    | Declaration.Module x, Declaration.Module y ->
      Identifier.equal x.identifier y.identifier
      && List.equal declaration_equal x.declarations y.declarations
    | Declaration.Comment x, Declaration.Comment y ->
      String.equal x.content y.content
    | _ -> false

  and signature_equal x y = List.equal declaration_equal x y
end
