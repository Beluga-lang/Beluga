(** Parser Syntax *)

(** The syntax for Beluga signatures after context-free parsing.

    OCaml constructor names prefixed with "Raw" require data-dependent
    disambiguation or reduction during the disambiguation to the external
    syntax. *)

open Support
open Beluga_syntax

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
      | Raw_identifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; prefixed : Bool.t
          }
          (** - [Raw_identifier { identifier = "x"; prefixed = false; _ }] is
                the variable or constant ["x"].
              - [Raw_identifier { identifier = "x"; prefixed = true; _ }] is
                the prefixed variable or constant ["(x)"].

              A prefixed constant may appear as an argument, or as applicand
              in prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | Raw_qualified_identifier of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          ; prefixed : Bool.t
          }
          (** - [Raw_qualified_identifier { identifier = "M.x"; prefixed = false; _ }]
                is the constant ["M.x"].
              - [Raw_qualified_identifier { identifier = "M.x"; prefixed = true; _ }]
                is the prefixed constant ["(M.x)"].

              Since identifiers are ambiguous with qualified identifiers in
              the parser, the following may be assumed during disambiguation:
              [List.length (Qualified_identifier.namespaces identifier) >= 1].

              A prefixed constant may appear as an argument, or as applicand
              in prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | Raw_type of { location : Location.t }
      | Raw_hole of { location : Location.t }
      | Raw_pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; plicity : Plicity.t
          ; body : Object.t
          }
          (** [Raw_pi { parameter_identifier = Option.Some "x"; parameter_sort = Option.Some t; body; _ }]
              is the Pi kind or type [{ x : t } body].

              It is a syntax error to omit the parameter sort. Implicit Pis
              currently do not have a corresponding syntax, but it may be
              added in the future. *)
      | Raw_lambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | Raw_arrow of
          { location : Location.t
          ; domain : Object.t
          ; range : Object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | Raw_annotated of
          { location : Location.t
          ; object_ : Object.t
          ; sort : Object.t
          }
      | Raw_application of
          { location : Location.t
          ; objects : Object.t List2.t
          }
          (** [Raw_application { objects; _ }] is the juxtaposition of
              [objects] delimited by whitespaces. [objects] may contain
              prefix, infix or postfix operators, along with operands. These
              are rewritten during the disambiguation to the external syntax. *)
  end =
    Object
end

(** {1 Parser Contextual LF Syntax} *)

(** The intermediate representation of contextual LF types, terms and
    patterns to delay the handling of data-dependent aspects of the grammar.

    This is LF augmented with substitutions, contexts and blocks. *)
module CLF = struct
  (** Contextual LF types, terms and patterns blurred together. *)
  module rec Object : sig
    type t =
      | Raw_identifier of
          { location : Location.t
          ; identifier : Identifier.t * [ `Plain | `Hash | `Dollar ]
          ; prefixed : Bool.t
          }
          (** - [Raw_identifier { identifier = "$x"; modifier = `Dollar; _ }]
                is the substitution variable ["$x"].
              - [Raw_identifier { identifier = "#x"; modifier = `Hash; _ }]
                is the parameter variable ["#x"].
              - [Raw_identifier { identifier = "x"; prefixed = false; _ }] is
                the variable or constant ["x"].
              - [Raw_identifier { identifier = "x"; prefixed = true; _ }] is
                the prefixed variable or constant ["(x)"].

              A prefixed constant may appear as an argument, or as applicand
              in prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | Raw_qualified_identifier of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          ; prefixed : Bool.t
          }
          (** - [Raw_qualified_identifier { identifier = "M.x"; prefixed = false; _ }]
                is the constant ["M.x"].
              - [Raw_qualified_identifier { identifier = "M.x"; prefixed = true; _ }]
                is the prefixed constant ["(M.x)"].

              Since identifiers are ambiguous with qualified identifiers in
              the parser, the following may be assumed during disambiguation:
              [List.length (Qualified_identifier.namespaces identifier) >= 1].

              Qualified identifiers are ambiguous with named projections.

              A prefixed constant may appear as an argument, or as applicand
              in prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | Raw_hole of
          { location : Location.t
          ; variant :
              [ `Underscore | `Unlabelled | `Labelled of Identifier.t ]
          }
      | Raw_pi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; plicity : Plicity.t
          ; body : Object.t
          }
          (** [Raw_pi { parameter_identifier = Option.Some "x"; parameter_sort = Option.Some t; body; _ }]
              is the Pi kind or type [{ x : t } body].

              It is a syntax error to omit the parameter sort. Implicit Pis
              currently do not have a corresponding syntax, but it may be
              added in the future. *)
      | Raw_lambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | Raw_arrow of
          { location : Location.t
          ; domain : Object.t
          ; range : Object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | Raw_annotated of
          { location : Location.t
          ; object_ : Object.t
          ; sort : Object.t
          }
      | Raw_application of
          { location : Location.t
          ; objects : Object.t List2.t
          }
          (** [Raw_application { objects; _ }] is the juxtaposition of
              [objects] delimited by whitespaces. [objects] may contain
              prefix, infix or postfix operators, along with operands. These
              are rewritten during the disambiguation to the external syntax. *)
      | Raw_block of
          { location : Location.t
          ; elements : (Identifier.t Option.t * Object.t) List1.t
          }
      | Raw_tuple of
          { location : Location.t
          ; elements : Object.t List1.t
          }
      | Raw_projection of
          { location : Location.t
          ; object_ : Object.t
          ; projection :
              [ `By_identifier of Identifier.t | `By_position of Int.t ]
          }
      | Raw_substitution of
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
      | Raw_constant of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          }
      | Raw_alternation of
          { location : Location.t
          ; schemas : Schema_object.t List2.t
          }
      | Raw_element of
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
end

(** {1 Parser Computation-Level Syntax} *)

(** The intermediate representation of computation-level kinds, types,
    expressions and patterns to delay the handling of data-dependent aspects
    of the grammar. *)
module Comp = struct
  (** Computational kinds and types blurred together. *)
  module rec Sort_object : sig
    type t =
      | Raw_identifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; prefixed : Bool.t
          }
      | Raw_qualified_identifier of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          ; prefixed : Bool.t
          }
      | Raw_ctype of { location : Location.t }
      | Raw_pi of
          { location : Location.t
          ; parameter_identifier :
              Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]
          ; parameter_sort : Meta.Thing.t Option.t
          ; plicity : Plicity.t
          ; body : Sort_object.t
          }
      | Raw_arrow of
          { location : Location.t
          ; domain : Sort_object.t
          ; range : Sort_object.t
          ; orientation : [ `Forward | `Backward ]
          }
      | Raw_cross of
          { location : Location.t
          ; operands : Sort_object.t List2.t
          }
      | Raw_box of
          { location : Location.t
          ; boxed : Meta.Thing.t
          }
      | Raw_application of
          { location : Location.t
          ; objects : Sort_object.t List2.t
          }
  end =
    Sort_object

  module rec Expression_object : sig
    type t =
      | Raw_identifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; prefixed : Bool.t
          }
      | Raw_qualified_identifier of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          ; prefixed : Bool.t
          }
          (** - [Raw_qualified_identifier { identifier = "M.x"; prefixed = false; _ }]
                is the constant ["M.x"].
              - [Raw_qualified_identifier { identifier = "M.x"; prefixed = true; _ }]
                is the prefixed constant ["(M.x)"].

              Since identifiers are ambiguous with qualified identifiers in
              the parser, the following may be assumed during disambiguation:
              [List.length (Qualified_identifier.namespaces identifier) >= 1].

              Qualified identifiers are ambiguous with observations.

              A prefixed constant may appear as an argument, or as applicand
              in prefix notation irrespective of its pre-defined fixity and
              associativity. *)
      | Raw_fn of
          { location : Location.t
          ; parameters : Identifier.t Option.t List1.t
          ; body : Expression_object.t
          }
      | Raw_mlam of
          { location : Location.t
          ; parameters :
              (Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]) List1.t
          ; body : Expression_object.t
          }
      | Raw_fun of
          { location : Location.t
          ; branches :
              (Meta.Context_object.t
              * Copattern_object.t List1.t
              * Expression_object.t)
              List1.t
          }
      | Raw_box of
          { location : Location.t
          ; meta_object : Meta.Thing.t
          }
      | Raw_let of
          { location : Location.t
          ; meta_context : Meta.Context_object.t
          ; pattern : Pattern_object.t
          ; scrutinee : Expression_object.t
          ; body : Expression_object.t
          }
      | Raw_impossible of
          { location : Location.t
          ; scrutinee : Expression_object.t
          }
      | Raw_case of
          { location : Location.t
          ; scrutinee : Expression_object.t
          ; check_coverage : Bool.t
          ; branches :
              (Meta.Context_object.t
              * Pattern_object.t
              * Expression_object.t)
              List1.t
          }
      | Raw_tuple of
          { location : Location.t
          ; elements : Expression_object.t List2.t
          }
      | Raw_hole of
          { location : Location.t
          ; label : Identifier.t Option.t
          }
      | Raw_box_hole of { location : Location.t }
      | Raw_application of
          { location : Location.t
          ; expressions : Expression_object.t List2.t
          }
      | Raw_annotated of
          { location : Location.t
          ; expression : Expression_object.t
          ; typ : Sort_object.t
          }
      | Raw_observation of
          { location : Location.t
          ; scrutinee : Expression_object.t
          ; destructor : Qualified_identifier.t
          }
          (** [Raw_observation { scrutinee = e; destructor = ".tl"; _ }] is
              the observation [e .tl].

              Because of the lexical convention, [destructor] may be multiple
              consecutive destructors. For instance, [(x) .tl .tl] has
              [destructor = ".tl.tl"]. *)
  end =
    Expression_object

  and Pattern_object : sig
    type t =
      | Raw_identifier of
          { location : Location.t
          ; identifier : Identifier.t
          ; prefixed : Bool.t
          }
      | Raw_qualified_identifier of
          { location : Location.t
          ; identifier : Qualified_identifier.t
          ; prefixed : Bool.t
          }
      | Raw_box of
          { location : Location.t
          ; pattern : Meta.Thing.t
          }
      | Raw_tuple of
          { location : Location.t
          ; elements : Pattern_object.t List2.t
          }
      | Raw_application of
          { location : Location.t
          ; patterns : Pattern_object.t List2.t
          }
      | Raw_annotated of
          { location : Location.t
          ; pattern : Pattern_object.t
          ; typ : Sort_object.t
          }
      | Raw_meta_annotated of
          { location : Location.t
          ; parameter_identifier :
              Identifier.t Option.t * [ `Plain | `Hash | `Dollar ]
          ; parameter_typ : Meta.Thing.t Option.t
          ; pattern : Pattern_object.t
          }
          (** [Raw_meta_annotated { paramter_identifier = Option.Some "x"; modifier; parameter_typ = Option.Some t; pattern; _ }]
              is the the pattern [{ x : t } pattern].

              It is a syntax error to omit the identifier or the type. *)
      | Raw_wildcard of { location : Location.t }
  end =
    Pattern_object

  and Copattern_object : sig
    type t =
      | Raw_observation of
          { location : Location.t
          ; observation : Qualified_identifier.t
          }
      | Raw_pattern of
          { location : Location.t
          ; pattern : Pattern_object.t
          }
  end =
    Copattern_object

  and Context_object : sig
    type t =
      { location : Location.t
      ; bindings : (Identifier.t * Sort_object.t Option.t) List.t
      }
  end =
    Context_object
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
          ; branches : Split_branch.t List1.t
          }
      | Impossible of
          { location : Location.t
          ; scrutinee : Comp.Expression_object.t
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
            ; identifier : Qualified_identifier.t
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

  module Repl = struct
    module Command = struct
      type t =
        (* Administrative commands *)
        | Rename of
            { location : Location.t
            ; rename_from : Identifier.t
            ; rename_to : Identifier.t
            ; level : [ `meta | `comp ]
            }
        | Toggle_automation of
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
            ; object_identifier : Qualified_identifier.t
            }
        | Select_theorem of
            { location : Location.t
            ; theorem : Qualified_identifier.t
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
            ; theorem : Qualified_identifier.t
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
        | Msplit of
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
  end
end

(** {1 Parser Signature Syntax} *)

(** The intermediate representation of Beluga signatures to delay the
    handling of data-dependent aspects of the grammar. *)
module Signature = struct
  module Pragma = struct
    type t =
      | Name of
          { location : Location.t
          ; constant : Qualified_identifier.t
          ; meta_variable_base : Identifier.t
          ; computation_variable_base : Identifier.t Option.t
          }
      | Default_associativity of
          { location : Location.t
          ; associativity : Associativity.t
          }
      | Prefix_fixity of
          { location : Location.t
          ; constant : Qualified_identifier.t
          ; precedence : Int.t Option.t
          }
      | Infix_fixity of
          { location : Location.t
          ; constant : Qualified_identifier.t
          ; precedence : Int.t Option.t
          ; associativity : Associativity.t Option.t
          }
      | Postfix_fixity of
          { location : Location.t
          ; constant : Qualified_identifier.t
          ; precedence : Int.t Option.t
          }
      | Not of { location : Location.t }
      | Open_module of
          { location : Location.t
          ; module_identifier : Qualified_identifier.t
          }
      | Abbreviation of
          { location : Location.t
          ; module_identifier : Qualified_identifier.t
          ; abbreviation : Identifier.t
          }
  end

  module rec Global_pragma : sig
    type t =
      | No_strengthening of { location : Location.t }
      | Warn_on_coverage_error of { location : Location.t }
      | Raise_error_on_coverage_error of { location : Location.t }
  end =
    Global_pragma

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
      | Raw_lf_typ_or_term_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ_or_const : LF.Object.t
          }
      | Raw_lf_typ_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : LF.Object.t
          }
      | Raw_lf_term_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : LF.Object.t
          }
      | Raw_inductive_comp_typ_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          }
      | Raw_stratified_comp_typ_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          }
      | Raw_comp_cotyp_constant of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          }
      | Raw_comp_expression_constructor of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          }
      | Raw_comp_expression_destructor of
          { location : Location.t
          ; identifier : Identifier.t
          ; observation_type : Comp.Sort_object.t
          ; return_type : Comp.Sort_object.t
          }
      | Raw_comp_typ_abbreviation of
          { location : Location.t
          ; identifier : Identifier.t
          ; kind : Comp.Sort_object.t
          ; typ : Comp.Sort_object.t
          }
      | Raw_schema of
          { location : Location.t
          ; identifier : Identifier.t
          ; schema : Meta.Schema_object.t
          }
      | Raw_theorem of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          ; order : Totality.Declaration.t Option.t
          ; body : Comp.Expression_object.t
          }
      | Raw_proof of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t
          ; order : Totality.Declaration.t Option.t
          ; body : Harpoon.Proof.t
          }
      | Raw_recursive_declarations of
          { location : Location.t
          ; declarations : Declaration.t List1.t
          }
      | Raw_val of
          { location : Location.t
          ; identifier : Identifier.t
          ; typ : Comp.Sort_object.t Option.t
          ; expression : Comp.Expression_object.t
          }
      | Raw_query of
          { location : Location.t
          ; identifier : Identifier.t Option.t
          ; meta_context : Meta.Context_object.t
          ; typ : LF.Object.t
          ; expected_solutions : Int.t Option.t
          ; maximum_tries : Int.t Option.t
          }
      | Raw_mquery of
          { location : Location.t
          ; identifier : Identifier.t Option.t
          ; typ : Comp.Sort_object.t
          ; expected_solutions : Int.t Option.t
          ; search_tries : Int.t Option.t
          ; search_depth : Int.t Option.t
          }
      | Raw_module of
          { location : Location.t
          ; identifier : Identifier.t
          ; declarations : Entry.t List.t
          }
  end =
    Declaration

  and Entry : sig
    type t =
      | Raw_declaration of
          { location : Location.t
          ; declaration : Declaration.t
          }
      | Raw_pragma of
          { location : Location.t
          ; pragma : Pragma.t
          }
      | Raw_comment of
          { location : Location.t
          ; content : String.t
          }
  end =
    Entry

  (** Parsed Beluga project *)
  type t =
    { global_pragmas : Global_pragma.t List.t
    ; entries : Entry.t List.t
    }
end

(** {1 Type Aliases} *)

(** {2 LF} *)

(** @canonical Synprs.lf_object *)
type lf_object = LF.Object.t

(** {2 Contextual LF} *)

(** @canonical Synprs.clf_object *)
type clf_object = CLF.Object.t

(** @canonical Synprs.clf_context_object *)
type clf_context_object = CLF.Context_object.t

(** {2 Meta-Level} *)

(** @canonical Synprs.meta_thing *)
type meta_thing = Meta.Thing.t

(** @canonical Synprs.meta_context_object *)
type meta_context_object = Meta.Context_object.t

(** @canonical Synprs.schema_object *)
type schema_object = Meta.Schema_object.t

(** {2 Computation-Level} *)

(** @canonical Synprs.comp_sort_object *)
type comp_sort_object = Comp.Sort_object.t

(** @canonical Synprs.comp_expression_object *)
type comp_expression_object = Comp.Expression_object.t

(** @canonical Synprs.comp_pattern_object *)
type comp_pattern_object = Comp.Pattern_object.t

(** @canonical Synprs.comp_copattern_object *)
type comp_copattern_object = Comp.Copattern_object.t

(** @canonical Synprs.comp_context_object *)
type comp_context_object = Comp.Context_object.t

(** {2 Harpoon} *)

(** @canonical Synprs.harpoon_proof *)
type harpoon_proof = Harpoon.Proof.t

(** @canonical Synprs.harpoon_command *)
type harpoon_command = Harpoon.Command.t

(** @canonical Synprs.harpoon_directive *)
type harpoon_directive = Harpoon.Directive.t

(** @canonical Synprs.harpoon_split_branch *)
type harpoon_split_branch = Harpoon.Split_branch.t

(** @canonical Synprs.harpoon_split_branch_label *)
type harpoon_split_branch_label = Harpoon.Split_branch.Label.t

(** @canonical Synprs.harpoon_suffices_branch *)
type harpoon_suffices_branch = Harpoon.Suffices_branch.t

(** @canonical Synprs.harpoon_hypothetical *)
type harpoon_hypothetical = Harpoon.Hypothetical.t

(** @canonical Synprs.harpoon_repl_command *)
type harpoon_repl_command = Harpoon.Repl.Command.t

(** {2 Signature} *)

(** @canonical Synprs.signature_pragma *)
type signature_pragma = Signature.Pragma.t

(** @canonical Synprs.signature_global_pragma *)
type signature_global_pragma = Signature.Global_pragma.t

(** @canonical Synprs.signature_totality_declaration *)
type signature_totality_declaration = Signature.Totality.Declaration.t

(** @canonical Synprs.'argument *)
type 'argument signature_totality_order =
  'argument Signature.Totality.Order.t

(** @canonical Synprs.signature_declaration *)
type signature_declaration = Signature.Declaration.t

(** @canonical Synprs.signature_entry *)
type signature_entry = Signature.Entry.t

(** @canonical Synprs.signature *)
type signature = Signature.t
