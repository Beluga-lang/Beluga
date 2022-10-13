(** Parser Syntax *)

(** The syntax for Beluga signatures after context-free parsing.

    OCaml constructor names prefixed with "Raw" require data-dependent
    disambiguation or reduction during the elaboration to the external
    syntax. *)

open Support

(** {1 Parser LF Syntax} *)

(** The intermediate representation of LF kinds, types and terms to delay the
    handling of data-dependent aspects of the grammar.

    The parsers associated with these types are only intended to be used in
    the definition of LF type-level or term-level constants. This is a weak,
    representational function space without case analysis or recursion. *)
module LF = struct
  (** LF kinds, types and terms blurred together. *)
  module rec Object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; quoted : Bool.t
          }
          (** - [RawIdentifier { identifier = "x"; quoted = false; _ }] is
                the variable or constant ["x"].
              - [RawIdentifier { identifier = "x"; quoted = true; _ }] is the
                quoted variable or constant ["(x)"].

              A quoted constant may appear as an argument, or as applicand in
              prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; quoted : Bool.t
          }
          (** - [RawQualifiedIdentifier { identifier = "M::x"; quoted = false; _ }]
                is the constant ["M::x"].
              - [RawQualifiedIdentifier { identifier = "M::x"; quoted = true; _ }]
                is the quoted constant ["(M::x)"].

              Since identifiers are ambiguous with qualified identifiers in
              the parser, the following may be assumed during disambiguation:
              [List.length (QualifiedIdentifier.modules identifier) >= 1].

              A quoted constant may appear as an argument, or as applicand in
              prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | RawType of { location : Location.t }
      | RawHole of { location : Location.t }
      | RawPi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
          (** [RawPi { parameter_identifier = Option.Some "x"; parameter_sort = Option.Some t; body; _ }]
              is the Pi kind or type [{ x : t } body].

              It is a syntax error to omit the parameter sort. *)
      | RawLambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawArrow of
          { location : Location.t
          ; domain : Object.t
          ; range : Object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | RawAnnotated of
          { location : Location.t
          ; object_ : Object.t
          ; sort : Object.t
          }
      | RawApplication of
          { location : Location.t
          ; objects : Object.t List2.t
          }
          (** [RawApplication { objects; _ }] is the juxtaposition of
              [objects] delimited by whitespaces. [objects] may contain
              prefix, infix or postfix operators, along with operands. These
              are rewritten during the elaboration to the external syntax. *)
  end =
    Object

  let location_of_object object_ =
    match object_ with
    | Object.RawIdentifier { location; _ }
    | Object.RawQualifiedIdentifier { location; _ }
    | Object.RawType { location; _ }
    | Object.RawHole { location; _ }
    | Object.RawPi { location; _ }
    | Object.RawLambda { location; _ }
    | Object.RawArrow { location; _ }
    | Object.RawAnnotated { location; _ }
    | Object.RawApplication { location; _ } -> location
end

(** {1 Parser Contextual LF Syntax} *)

(** The intermediate representation of contextual LF types, terms and
    patterns to delay the handling of data-dependent aspects of the grammar.

    This is LF augmented with substitutions, contexts and blocks. *)
module CLF = struct
  (** Contextual LF types, terms and patterns blurred together. *)
  module rec Object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t * [ `Plain | `Hash | `Dollar ]
          ; quoted : Bool.t
          }
          (** - [RawIdentifier { identifier = "$x"; modifier = `Dollar; _ }]
                is the substitution variable ["$x"].
              - [RawIdentifier { identifier = "#x"; modifier = `Hash; _ }] is
                the parameter variable ["#x"].
              - [RawIdentifier { identifier = "x"; quoted = false; _ }] is
                the variable or constant ["x"].
              - [RawIdentifier { identifier = "x"; quoted = true; _ }] is the
                quoted variable or constant ["(x)"].

              A quoted constant may appear as an argument, or as applicand in
              prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; quoted : Bool.t
          }
          (** - [RawQualifiedIdentifier { identifier = "M::x"; quoted = false; _ }]
                is the constant ["M::x"].
              - [RawQualifiedIdentifier { identifier = "M::x"; quoted = true; _ }]
                is the quoted constant ["(M::x)"].

              Since identifiers are ambiguous with qualified identifiers in
              the parser, the following may be assumed during disambiguation:
              [List.length (QualifiedIdentifier.modules identifier) >= 1].

              A quoted constant may appear as an argument, or as applicand in
              prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | RawHole of
          { location : Location.t
          ; variant :
              [ `Underscore | `Unlabelled | `Labelled of Identifier.t ]
          }
      | RawPi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
          (** [RawPi { parameter_identifier = Option.Some "x"; parameter_sort = Option.Some t; body; _ }]
              is the Pi kind or type [{ x : t } body].

              It is a syntax error to omit the parameter sort. *)
      | RawLambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawArrow of
          { location : Location.t
          ; domain : Object.t
          ; range : Object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | RawAnnotated of
          { location : Location.t
          ; object_ : Object.t
          ; sort : Object.t
          }
      | RawApplication of
          { location : Location.t
          ; objects : Object.t List2.t
          }
          (** [RawApplication { objects; _ }] is the juxtaposition of
              [objects] delimited by whitespaces. [objects] may contain
              prefix, infix or postfix operators, along with operands. These
              are rewritten during the elaboration to the external syntax. *)
      | RawBlock of
          { location : Location.t
          ; elements : (Identifier.t Option.t * Object.t) List1.t
          }
      | RawTuple of
          { location : Location.t
          ; elements : Object.t List1.t
          }
      | RawProjection of
          { location : Location.t
          ; object_ : Object.t
          ; projection :
              [ `By_identifier of Identifier.t | `By_position of Int.t ]
          }
      | RawSubstitution of
          { location : Location.t
          ; object_ : Object.t
          ; substitution : Context_object.t
          }
  end =
    Object

  (** Contextual LF substitutions and contexts blurred together. *)
  and Context_object : sig
    type t =
      { location : Location.t
      ; head : Context_object.Head.t
      ; objects : (Identifier.t Option.t * Object.t) List.t
      }

    module Head : sig
      type t =
        | None of { location : Location.t }
        | Identity of { location : Location.t }
    end
  end =
    Context_object

  let location_of_object object_ =
    match object_ with
    | Object.RawIdentifier { location; _ }
    | Object.RawQualifiedIdentifier { location; _ }
    | Object.RawHole { location; _ }
    | Object.RawPi { location; _ }
    | Object.RawLambda { location; _ }
    | Object.RawArrow { location; _ }
    | Object.RawAnnotated { location; _ }
    | Object.RawApplication { location; _ }
    | Object.RawBlock { location; _ }
    | Object.RawTuple { location; _ }
    | Object.RawProjection { location; _ }
    | Object.RawSubstitution { location; _ } -> location

  let location_of_context_object context_object =
    match context_object with
    | { Context_object.location; _ } -> location
end

(** {1 Parser Meta-Level Syntax} *)

(** The intermediate representation of meta-types, meta-objects and
    meta-patterns to delay the handling of data-dependent aspects of the
    grammar. *)
module Meta = struct
  (** Meta-objects, meta-types, meta-patterns. *)
  module rec Thing : sig
    type t =
      | RawSchema of
          { location : Location.t
          ; schema : Schema_object.t
          }  (** [RawSchema { schema; _ }] is the context schema [schema]. *)
      | RawContext of
          { location : Location.t
          ; context : CLF.Context_object.t
          }
          (** [RawPlain { context; _ }] is the boxed contextual LF context
              [\[context\]]. *)
      | RawTurnstile of
          { location : Location.t
          ; context : CLF.Context_object.t
          ; object_ : CLF.Context_object.t
          ; variant : [ `Plain | `Hash | `Dollar | `Dollar_hash ]
          }
          (** - [RawTurnstile { context; variant = `Plain; object_; _ } ] is
                the meta-thing [\[context |- object_\]] or
                [(context |- object_)].
              - [RawTurnstile { context; variant = `Hash; object_; _ } ] is
                the meta-thing [#\[context |- object_\]] or
                [#(context |- object_)].
              - [RawTurnstile { context; variant = `Dollar; object_; _ } ] is
                the meta-thing [$\[context |- object_\]] or
                [$(context |- object_)].
              - [RawTurnstile { context; variant = `Dollar_hash; object_; _ } ]
                is the meta-thing [$\[context |-# object_\]] or
                [$(context |-# object_)]. *)
  end =
    Thing

  (** Context schemas. *)
  and Schema_object : sig
    type t =
      | RawConstant of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
      | RawAlternation of
          { location : Location.t
          ; schemas : Schema_object.t List2.t
          }
      | RawElement of
          { location : Location.t
          ; some : (Identifier.t * CLF.Object.t) List1.t Option.t
          ; block : (Identifier.t Option.t * CLF.Object.t) List1.t
          }
  end =
    Schema_object

  (** Meta-contexts. *)
  and Context_object : sig
    type t =
      { location : Location.t
      ; bindings :
          ((Identifier.t * [ `Plain | `Hash | `Dollar ]) * Thing.t Option.t)
          List.t
      }
  end =
    Context_object

  let location_of_meta_thing meta_thing =
    match meta_thing with
    | Thing.RawSchema { location; _ }
    | Thing.RawContext { location; _ }
    | Thing.RawTurnstile { location; _ } -> location

  let location_of_schema_object schema_object =
    match schema_object with
    | Schema_object.RawConstant { location; _ }
    | Schema_object.RawAlternation { location; _ }
    | Schema_object.RawElement { location; _ } -> location

  let location_of_context_object context_object =
    match context_object with
    | { Context_object.location; _ } -> location
end

(** {1 Parser Computation-Level Syntax} *)

(** The intermediate representation of computation-level kinds, types,
    expressions and patterns to delay the handling of data-dependent aspects
    of the grammar. *)
module Comp = struct
  (** Computational kinds and types blurred together. *)
  module rec Sort_object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; quoted : Bool.t
          }
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; quoted : Bool.t
          }
      | RawCtype of { location : Location.t }
      | RawPi of
          { location : Location.t
          ; parameter_identifier :
              Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]
          ; parameter_sort : Meta.Thing.t Option.t
          ; plicity : Plicity.t
          ; body : Sort_object.t
          }
      | RawArrow of
          { location : Location.t
          ; domain : Sort_object.t
          ; range : Sort_object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | RawCross of
          { location : Location.t
          ; operands : Sort_object.t List2.t
          }
      | RawBox of
          { location : Location.t
          ; boxed : Meta.Thing.t
          }
      | RawApplication of
          { location : Location.t
          ; objects : Sort_object.t List2.t
          }
  end =
    Sort_object

  module rec Expression_object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; quoted : Bool.t
          }
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; quoted : Bool.t
          ; observation : Bool.t
          }
      | RawFn of
          { location : Location.t
          ; parameters : Identifier.t Option.t List1.t
          ; body : Expression_object.t
          }
      | RawMlam of
          { location : Location.t
          ; parameters :
              (Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]) List1.t
          ; body : Expression_object.t
          }
      | RawFun of
          { location : Location.t
          ; branches :
              (Pattern_object.t List1.t * Expression_object.t) List1.t
          }
      | RawBox of
          { location : Location.t
          ; meta_object : Meta.Thing.t
          }
      | RawLet of
          { location : Location.t
          ; pattern : Pattern_object.t
          ; scrutinee : Expression_object.t
          ; body : Expression_object.t
          }
      | RawImpossible of
          { location : Location.t
          ; scrutinee : Expression_object.t
          }
      | RawCase of
          { location : Location.t
          ; scrutinee : Expression_object.t
          ; check_coverage : Bool.t
          ; branches : (Pattern_object.t * Expression_object.t) List1.t
          }
      | RawTuple of
          { location : Location.t
          ; elements : Expression_object.t List2.t
          }
      | RawHole of
          { location : Location.t
          ; label : Identifier.t Option.t
          }
      | RawBoxHole of { location : Location.t }
      | RawApplication of
          { location : Location.t
          ; expressions : Expression_object.t List2.t
          }
          (** [Application { expressions; _ }] is the computational
              expression-level juxtaposition of [expressions].

              If
              [expressions = RawQualifiedIdentifier { observation = true; _ } :: xs],
              then the application is actually an observation. *)
      | RawAnnotated of
          { location : Location.t
          ; expression : Expression_object.t
          ; typ : Sort_object.t
          }
  end =
    Expression_object

  and Pattern_object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; quoted : Bool.t
          }
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          ; quoted : Bool.t
          ; observation : Bool.t
          }
      | RawBox of
          { location : Location.t
          ; pattern : Meta.Thing.t
          }
      | RawTuple of
          { location : Location.t
          ; elements : Pattern_object.t List2.t
          }
      | RawApplication of
          { location : Location.t
          ; patterns : Pattern_object.t List2.t
          }
      | RawObservation of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; arguments : Pattern_object.t List.t
          }
      | RawAnnotated of
          { location : Location.t
          ; pattern : Pattern_object.t
          ; typ : Sort_object.t
          }
      | RawMetaAnnotated of
          { location : Location.t
          ; parameter_identifier :
              Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]
          ; parameter_typ : Meta.Thing.t Option.t
          ; pattern : Pattern_object.t
          }
          (** [RawMetaAnnotated { paramter_identifier = Option.Some "x"; modifier; parameter_typ = Option.Some t; pattern; _ }]
              is the the pattern [{ x : t } pattern].

              It is a syntax error to omit the identifier or the type. *)
      | RawWildcard of { location : Location.t }
  end =
    Pattern_object

  and Context_object : sig
    type t =
      { location : Location.t
      ; bindings : (Identifier.t * Sort_object.t Option.t) List.t
      }
  end =
    Context_object

  let location_of_sort_object sort_object =
    match sort_object with
    | Sort_object.RawIdentifier { location; _ }
    | Sort_object.RawQualifiedIdentifier { location; _ }
    | Sort_object.RawCtype { location; _ }
    | Sort_object.RawPi { location; _ }
    | Sort_object.RawArrow { location; _ }
    | Sort_object.RawCross { location; _ }
    | Sort_object.RawBox { location; _ }
    | Sort_object.RawApplication { location; _ } -> location

  let location_of_expression_object expression_object =
    match expression_object with
    | Expression_object.RawIdentifier { location; _ }
    | Expression_object.RawQualifiedIdentifier { location; _ }
    | Expression_object.RawFn { location; _ }
    | Expression_object.RawMlam { location; _ }
    | Expression_object.RawFun { location; _ }
    | Expression_object.RawBox { location; _ }
    | Expression_object.RawLet { location; _ }
    | Expression_object.RawImpossible { location; _ }
    | Expression_object.RawCase { location; _ }
    | Expression_object.RawTuple { location; _ }
    | Expression_object.RawHole { location; _ }
    | Expression_object.RawBoxHole { location; _ }
    | Expression_object.RawApplication { location; _ }
    | Expression_object.RawAnnotated { location; _ } -> location

  let location_of_pattern_object pattern_object =
    match pattern_object with
    | Pattern_object.RawIdentifier { location; _ }
    | Pattern_object.RawQualifiedIdentifier { location; _ }
    | Pattern_object.RawBox { location; _ }
    | Pattern_object.RawTuple { location; _ }
    | Pattern_object.RawApplication { location; _ }
    | Pattern_object.RawObservation { location; _ }
    | Pattern_object.RawAnnotated { location; _ }
    | Pattern_object.RawMetaAnnotated { location; _ }
    | Pattern_object.RawWildcard { location; _ } -> location
end

(** {1 Parser Harpoon Syntax} *)

(** The intermediate representation of Harpoon proof scripts and REPL
    commands to delay the handling of data-dependent aspects of the grammar. *)
module Harpoon = struct
  module rec Proof : sig
    type t =
      | Incomplete of
          { location : Location.t
          ; label : Identifier.t Option.t
          }
      | Command of
          { location : Location.t
          ; command : Command.t
          ; body : Proof.t
          }
      | Directive of
          { location : Location.t
          ; directive : Directive.t
          }
  end =
    Proof

  and Command : sig
    type t =
      | By of
          { location : Location.t
          ; expression : Comp.Expression_object.t
          ; assignee : Identifier.t
          }
      | Unbox of
          { location : Location.t
          ; expression : Comp.Expression_object.t
          ; assignee : Identifier.t
          ; modifier : [ `Strengthened ] Option.t
          }
  end =
    Command

  and Directive : sig
    type t =
      | Intros of
          { location : Location.t
          ; hypothetical : Hypothetical.t
          }
      | Solve of
          { location : Location.t
          ; solution : Comp.Expression_object.t
          }
      | Split of
          { location : Location.t
          ; scrutinee : Comp.Expression_object.t
          ; branches : Split_branch.t List.t
          }
      | Suffices of
          { location : Location.t
          ; scrutinee : Comp.Expression_object.t
          ; branches : Suffices_branch.t List.t
          }
  end =
    Directive

  and Split_branch : sig
    type t =
      { location : Location.t
      ; label : Split_branch.Label.t
      ; body : Hypothetical.t
      }

    module Label : sig
      type t =
        | Constant of
            { location : Location.t
            ; identifier : QualifiedIdentifier.t
            }
        | Bound_variable of { location : Location.t }
        | Empty_context of { location : Location.t }
        | Extended_context of
            { location : Location.t
            ; schema_element : Int.t  (** 1-based *)
            }
        | Parameter_variable of
            { location : Location.t
            ; schema_element : Int.t  (** 1-based *)
            ; projection : Int.t Option.t  (** 1-based *)
            }
    end
  end =
    Split_branch

  and Suffices_branch : sig
    type t =
      { location : Location.t
      ; goal : Comp.Sort_object.t
      ; proof : Proof.t
      }
  end =
    Suffices_branch

  and Hypothetical : sig
    type t =
      { location : Location.t
      ; meta_context : Meta.Context_object.t
      ; comp_context : Comp.Context_object.t
      ; proof : Proof.t
      }
  end =
    Hypothetical

  module rec Repl : sig
    module Command : sig
      type t =
        (* Administrative commands *)
        | Rename of
            { location : Location.t
            ; rename_from : Identifier.t
            ; rename_to : Identifier.t
            ; level : [ `meta | `comp ]
            }
        | ToggleAutomation of
            { location : Location.t
            ; kind : [ `auto_intros | `auto_solve_trivial ]
            ; change : [ `on | `off | `toggle ]
            }
        | Type of
            { location : Location.t
            ; scrutinee : Comp.Expression_object.t
            }
        | Info of
            { location : Location.t
            ; kind : [ `prog ]
            ; object_identifier : QualifiedIdentifier.t
            }
        | SelectTheorem of
            { location : Location.t
            ; theorem : QualifiedIdentifier.t
            }
        | Theorem of
            { location : Location.t
            ; subcommand :
                [ `list
                | `defer
                | `show_ihs
                | `show_proof
                | `dump_proof of String.t  (** File path *)
                ]
            }
        | Session of
            { location : Location.t
            ; subcommand : [ `list | `defer | `create | `serialize ]
            }
        | Subgoal of
            { location : Location.t
            ; subcommand : [ `list | `defer ]
            }
        | Undo of { location : Location.t }
        | Redo of { location : Location.t }
        | History of { location : Location.t }
        | Translate of
            { location : Location.t
            ; theorem : QualifiedIdentifier.t
            }
        (* Actual tactics *)
        | Intros of
            { location : Location.t
            ; introduced_variables : Identifier.t List1.t Option.t
            }
        | Split of
            { location : Location.t
            ; scrutinee : Comp.Expression_object.t
            }
        | Invert of
            { location : Location.t
            ; scrutinee : Comp.Expression_object.t
            }
        | Impossible of
            { location : Location.t
            ; scrutinee : Comp.Expression_object.t
            }
        | MSplit of
            { location : Location.t
            ; identifier : Identifier.t * [ `Plain | `Hash | `Dollar ]
            }
        | Solve of
            { location : Location.t
            ; solution : Comp.Expression_object.t
            }
        | Unbox of
            { location : Location.t
            ; expression : Comp.Expression_object.t
            ; assignee : Identifier.t
            ; modifier : [ `Strengthened ] Option.t
            }
        | By of
            { location : Location.t
            ; expression : Comp.Expression_object.t
            ; assignee : Identifier.t
            }
        | Suffices of
            { location : Location.t
            ; implication : Comp.Expression_object.t
            ; goal_premises :
                [ `exact of Comp.Sort_object.t | `infer of Location.t ]
                List.t
            }
        | Help of { location : Location.t }
    end
  end =
    Repl

  let location_of_proof proof =
    match proof with
    | Proof.Incomplete { location; _ }
    | Proof.Command { location; _ }
    | Proof.Directive { location; _ } -> location

  let location_of_command command =
    match command with
    | Command.By { location; _ } | Command.Unbox { location; _ } -> location

  let location_of_directive directive =
    match directive with
    | Directive.Intros { location; _ }
    | Directive.Solve { location; _ }
    | Directive.Split { location; _ }
    | Directive.Suffices { location; _ } -> location

  let location_of_split_branch split_branch =
    match split_branch with
    | { Split_branch.location; _ } -> location

  let location_of_split_branch_label split_branch_label =
    match split_branch_label with
    | Split_branch.Label.Constant { location; _ }
    | Split_branch.Label.Bound_variable { location; _ }
    | Split_branch.Label.Empty_context { location; _ }
    | Split_branch.Label.Extended_context { location; _ }
    | Split_branch.Label.Parameter_variable { location; _ } -> location

  let location_of_suffices_branch suffices_branch =
    match suffices_branch with
    | { Suffices_branch.location; _ } -> location

  let location_of_hypothetical hypothetical =
    match hypothetical with
    | { Hypothetical.location; _ } -> location

  let location_of_repl_command repl_command =
    match repl_command with
    | Repl.Command.Rename { location; _ }
    | Repl.Command.ToggleAutomation { location; _ }
    | Repl.Command.Type { location; _ }
    | Repl.Command.Info { location; _ }
    | Repl.Command.SelectTheorem { location; _ }
    | Repl.Command.Theorem { location; _ }
    | Repl.Command.Session { location; _ }
    | Repl.Command.Subgoal { location; _ }
    | Repl.Command.Undo { location; _ }
    | Repl.Command.Redo { location; _ }
    | Repl.Command.History { location; _ }
    | Repl.Command.Translate { location; _ }
    | Repl.Command.Intros { location; _ }
    | Repl.Command.Split { location; _ }
    | Repl.Command.Invert { location; _ }
    | Repl.Command.Impossible { location; _ }
    | Repl.Command.MSplit { location; _ }
    | Repl.Command.Solve { location; _ }
    | Repl.Command.Unbox { location; _ }
    | Repl.Command.By { location; _ }
    | Repl.Command.Suffices { location; _ }
    | Repl.Command.Help { location; _ } -> location
end

(** {1 Parser Signature Syntax} *)

(** The intermediate representation of Beluga signatures to delay the
    handling of data-dependent aspects of the grammar. *)
module Signature = struct
  module Pragma = struct
    type t =
      | Name of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; meta_variable_base : Identifier.t
          ; computation_variable_base : Identifier.t Option.t
          }
      | Default_associativity of
          { location : Location.t
          ; associativity : Associativity.t
          }
      | Prefix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          }
      | Infix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          ; associativity : Associativity.t Option.t
          }
      | Postfix_fixity of
          { location : Location.t
          ; constant : QualifiedIdentifier.t
          ; precedence : Int.t
          }
      | Not of { location : Location.t }
      | Open_module of
          { location : Location.t
          ; module_identifier : QualifiedIdentifier.t
          }
      | Abbreviation of
          { location : Location.t
          ; module_identifier : QualifiedIdentifier.t
          ; abbreviation : Identifier.t
          }

    module Global = struct
      type t =
        | No_strengthening of { location : Location.t }
        | Coverage of
            { location : Location.t
            ; variant : [ `Error | `Warn ]
            }
    end
  end

  module rec Totality : sig
    module rec Declaration : sig
      type t =
        | Trust of { location : Location.t }
        | Numeric of
            { location : Location.t
            ; order : Int.t Order.t Option.t
            }
        | Named of
            { location : Location.t
            ; order : Identifier.t Order.t Option.t
            ; program : Identifier.t
            ; argument_labels : Identifier.t Option.t List.t
            }
    end

    and Order : sig
      type 'a t =
        | Argument of
            { location : Location.t
            ; argument : 'a
            }
        | Lexical_ordering of
            { location : Location.t
            ; arguments : 'a Order.t List1.t
            }
        | Simultaneous_ordering of
            { location : Location.t
            ; arguments : 'a Order.t List1.t
            }
    end
  end =
    Totality

  module rec Declaration : sig
    type t =
      | Typ_or_const of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ_or_const : LF.Object.t
          }
      | Typ of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : LF.Object.t
          }
      | Const of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : LF.Object.t
          }
      | CompTyp of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          ; datatype_flavour : [ `Inductive | `Stratified ]
          }
      | CompCotyp of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          }
      | CompConst of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          }
      | CompDest of
          { location : Location.t
          ; identifier : Identifier.t
          ; observation_type : Comp.Sort_object.t
          ; return_type : Comp.Sort_object.t
          }
      | CompTypAbbrev of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          ; typ : Comp.Sort_object.t
          }
      | Schema of
          { location : Location.t
          ; identifier : Identifier.t
          ; schema : Meta.Schema_object.t
          }
      | Pragma of
          { location : Location.t
          ; pragma : Pragma.t
          }
      | GlobalPragma of
          { location : Location.t
          ; pragma : Pragma.Global.t
          }
      | Theorem of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          ; order : Totality.Declaration.t Option.t
          ; body : Comp.Expression_object.t
          }
      | Proof of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          ; order : Totality.Declaration.t Option.t
          ; body : Harpoon.Proof.t
          }
      | Recursive_declarations of
          { location : Location.t
          ; declarations : Declaration.t List1.t
          }
      | Val of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t Option.t
          ; expression : Comp.Expression_object.t
          }
      | Query of
          { location : Location.t
          ; identifier : Identifier.t Option.t
          ; meta_context : Meta.Context_object.t
          ; typ : LF.Object.t
          ; expected_solutions : Int.t Option.t
          ; maximum_tries : Int.t Option.t
          }
      | MQuery of
          { location : Location.t
          ; identifier : Identifier.t Option.t
          ; typ : Comp.Sort_object.t
          ; expected_solutions : Int.t Option.t
          ; search_tries : Int.t Option.t
          ; search_depth : Int.t Option.t
          }
      | Module of
          { location : Location.t
          ; identifier : Identifier.t
          ; declarations : Declaration.t List.t
          }
      | Comment of
          { location : Location.t
          ; content : String.t
          }
  end =
    Declaration

  (** Parsed Beluga project *)
  type t = Declaration.t List.t

  let location_of_pragma pragma =
    match pragma with
    | Pragma.Name { location; _ }
    | Pragma.Default_associativity { location; _ }
    | Pragma.Prefix_fixity { location; _ }
    | Pragma.Infix_fixity { location; _ }
    | Pragma.Postfix_fixity { location; _ }
    | Pragma.Not { location; _ }
    | Pragma.Open_module { location; _ }
    | Pragma.Abbreviation { location; _ } -> location

  let location_of_global_pragma global_pragma =
    match global_pragma with
    | Pragma.Global.No_strengthening { location; _ }
    | Pragma.Global.Coverage { location; _ } -> location

  let location_of_totality_declaration totality_declaration =
    match totality_declaration with
    | Totality.Declaration.Trust { location; _ }
    | Totality.Declaration.Numeric { location; _ }
    | Totality.Declaration.Named { location; _ } -> location

  let location_of_totality_order totality_order =
    match totality_order with
    | Totality.Order.Argument { location; _ }
    | Totality.Order.Lexical_ordering { location; _ }
    | Totality.Order.Simultaneous_ordering { location; _ } -> location

  let location_of_declaration declaration =
    match declaration with
    | Declaration.Typ_or_const { location; _ }
    | Declaration.Typ { location; _ }
    | Declaration.Const { location; _ }
    | Declaration.CompTyp { location; _ }
    | Declaration.CompCotyp { location; _ }
    | Declaration.CompConst { location; _ }
    | Declaration.CompDest { location; _ }
    | Declaration.CompTypAbbrev { location; _ }
    | Declaration.Schema { location; _ }
    | Declaration.Pragma { location; _ }
    | Declaration.GlobalPragma { location; _ }
    | Declaration.Theorem { location; _ }
    | Declaration.Proof { location; _ }
    | Declaration.Recursive_declarations { location; _ }
    | Declaration.Val { location; _ }
    | Declaration.Query { location; _ }
    | Declaration.MQuery { location; _ }
    | Declaration.Module { location; _ }
    | Declaration.Comment { location; _ } -> location
end
