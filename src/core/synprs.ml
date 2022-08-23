(** Parser Syntax *)

open Support

(** {1 Parser LF Syntax}

    The intermediate representation of LF kinds, types and terms to delay the
    handling of data-dependent aspects of the grammar.

    OCaml constructor names prefixed with `Raw' require data-dependent
    disambiguation or reduction during the elaboration to the external
    syntax.

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
          }
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
      | RawType of { location : Location.t }
      | RawHole of { location : Location.t }
      | RawPi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawLambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawArrow of
          { location : Location.t
          ; orientation : [ `Forward | `Backward ]
          ; left_operand : Object.t
          ; right_operand : Object.t
          }
          (** [RawArrow { left_operand = a; orientation = `Forward; right_operand = b; _ }]
              is the object `a -> b'.
              [RawArrow { left_operand = a; orientation = `Backward; right_operand = b; _ }]
              is the object `a <- b'.

              Right arrows are right-associative, and left arrows are
              left-associative.

              Both arrows are parsed as right-associative because the parser
              does not perform bottom-up parsing. They are disentangled in
              the elaboration to the external syntax. *)
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
      | RawParenthesized of
          { location : Location.t
          ; object_ : Object.t
          }
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
    | Object.RawApplication { location; _ }
    | Object.RawParenthesized { location; _ } -> location

  let rec pp_object ppf object_ =
    match object_ with
    | Object.RawIdentifier { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Object.RawQualifiedIdentifier { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Object.RawType _ -> Format.fprintf ppf "type"
    | Object.RawHole _ -> Format.fprintf ppf "_"
    | Object.RawPi
        { parameter_identifier = Option.None
        ; parameter_sort = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>{@ _@ }@ %a@]" pp_object body
    | Object.RawPi
        { parameter_identifier = Option.None
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ _@ :@ %a@ }@ %a@]" pp_object parameter_sort
        pp_object body
    | Object.RawPi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_object body
    | Object.RawPi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>{@ %a@ :@ %a@ }@ %a@]" Identifier.pp
        parameter_identifier pp_object parameter_sort pp_object body
    | Object.RawLambda
        { parameter_identifier = Option.None
        ; parameter_sort = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>\\_.@ %a@]" pp_object body
    | Object.RawLambda
        { parameter_identifier = Option.None
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\_:%a.@ %a@]" pp_object parameter_sort
        pp_object body
    | Object.RawLambda
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a.@ %a@]" Identifier.pp
        parameter_identifier pp_object body
    | Object.RawLambda
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>\\%a:%a.@ %a@]" Identifier.pp
        parameter_identifier pp_object parameter_sort pp_object body
    | Object.RawArrow
        { left_operand; right_operand; orientation = `Forward; _ } ->
      Format.fprintf ppf "@[<2>%a@ ->@ %a@]" pp_object left_operand pp_object
        right_operand
    | Object.RawArrow
        { left_operand; right_operand; orientation = `Backward; _ } ->
      Format.fprintf ppf "@[<2>%a@ <-@ %a@]" pp_object left_operand pp_object
        right_operand
    | Object.RawAnnotated { object_; sort; _ } ->
      Format.fprintf ppf "@[<2>%a@ :@ %a@]" pp_object object_ pp_object sort
    | Object.RawApplication { objects; _ } ->
      Format.fprintf ppf "@[<2>%a@]"
        (List2.pp ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") pp_object)
        objects
    | Object.RawParenthesized { object_; _ } ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_object object_

  let rec pp_object_debug ppf object_ =
    match object_ with
    | Object.RawIdentifier { identifier; _ } ->
      Format.fprintf ppf "%a" Identifier.pp identifier
    | Object.RawQualifiedIdentifier { identifier; _ } ->
      Format.fprintf ppf "%a" QualifiedIdentifier.pp identifier
    | Object.RawType _ -> Format.fprintf ppf "type"
    | Object.RawHole _ -> Format.fprintf ppf "_"
    | Object.RawPi
        { parameter_identifier = Option.None
        ; parameter_sort = Option.None
        ; body
        ; _
        } -> Format.fprintf ppf "@[<2>Pi({@ _@ }@ %a)@]" pp_object_debug body
    | Object.RawPi
        { parameter_identifier = Option.None
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Pi({@ _@ :@ %a@ }@ %a)@]" pp_object_debug
        parameter_sort pp_object_debug body
    | Object.RawPi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Pi({@ %a@ }@ %a)@]" Identifier.pp
        parameter_identifier pp_object_debug body
    | Object.RawPi
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Pi({@ %a@ :@ %a@ }@ %a)@]" Identifier.pp
        parameter_identifier pp_object_debug parameter_sort pp_object_debug
        body
    | Object.RawLambda
        { parameter_identifier = Option.None
        ; parameter_sort = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Lambda(\\_.@ %a)@]" pp_object_debug body
    | Object.RawLambda
        { parameter_identifier = Option.None
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Lambda(\\_:%a.@ %a)@]" pp_object_debug
        parameter_sort pp_object_debug body
    | Object.RawLambda
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.None
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Lambda(\\%a.@ %a)@]" Identifier.pp
        parameter_identifier pp_object_debug body
    | Object.RawLambda
        { parameter_identifier = Option.Some parameter_identifier
        ; parameter_sort = Option.Some parameter_sort
        ; body
        ; _
        } ->
      Format.fprintf ppf "@[<2>Lambda(\\%a:%a.@ %a)@]" Identifier.pp
        parameter_identifier pp_object_debug parameter_sort pp_object_debug
        body
    | Object.RawArrow
        { left_operand; right_operand; orientation = `Forward; _ } ->
      Format.fprintf ppf "@[<2>ForwardArrow(%a@ ->@ %a)@]" pp_object_debug
        left_operand pp_object_debug right_operand
    | Object.RawArrow
        { left_operand; right_operand; orientation = `Backward; _ } ->
      Format.fprintf ppf "@[<2>BackwardArrow(%a@ <-@ %a)@]" pp_object_debug
        left_operand pp_object_debug right_operand
    | Object.RawAnnotated { object_; sort; _ } ->
      Format.fprintf ppf "@[<2>Annotated(%a@ :@ %a)@]" pp_object_debug
        object_ pp_object_debug sort
    | Object.RawApplication { objects; _ } ->
      Format.fprintf ppf "@[<2>Application(%a)@]"
        (List2.pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           pp_object_debug)
        objects
    | Object.RawParenthesized { object_; _ } ->
      Format.fprintf ppf "@[<2>Parenthesized(%a)@]" pp_object_debug object_
end

(** {1 Parser Contextual LF Syntax}

    The intermediate representation of contextual LF types, terms and
    patterns to delay the handling of data-dependent aspects of the grammar.

    OCaml constructor names prefixed with `Raw' require data-dependent
    disambiguation or reduction during the elaboration to the external
    syntax.

    This is LF augmented with substitutions and blocks. *)
module CLF = struct
  (** Contextual LF types, terms and patterns blurred together. *)
  module rec Object : sig
    type t =
      | RawIdentifier of
          { location : Location.t
          ; identifier : Identifier.t
          }
      | RawQualifiedIdentifier of
          { location : Location.t
          ; identifier : QualifiedIdentifier.t
          }
      | RawHole of { location : Location.t }
      | RawPi of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawLambda of
          { location : Location.t
          ; parameter_identifier : Identifier.t Option.t
          ; parameter_sort : Object.t Option.t
          ; body : Object.t
          }
      | RawArrow of
          { location : Location.t
          ; left_operand : Object.t
          ; right_operand : Object.t
          ; orientation : [ `Forward | `Backward ]
          }
          (** [RawArrow { left_operand = a; orientation = `Forward; right_operand = b; _ }]
              is the object `a -> b'.
              [RawArrow { left_operand = a; orientation = `Backward; right_operand = b; _ }]
              is the object `a <- b'.

              Right arrows are right-associative, and left arrows are
              left-associative.

              Both arrows are parsed as right-associative because the parser
              does not perform bottom-up parsing. They are disentangled in
              the elaboration to the external syntax. *)
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
          ; elements :
              (Identifier.t Option.t * Object.t)
              * (Identifier.t * Object.t) List.t
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
          ; substitution : Substitution.t
          }
      | RawParenthesized of
          { location : Location.t
          ; object_ : Object.t
          }
  end =
    Object

  and Substitution : sig
    type t =
      | Empty of { location : Location.t }
      | Identity of { location : Location.t }
      | Substitution of
          { location : Location.t
          ; extends_identity : Bool.t
          ; objects : Object.t List1.t
          }
  end =
    Substitution

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
    | Object.RawSubstitution { location; _ }
    | Object.RawParenthesized { location; _ } -> location
end

(** {1 Parser Computation Syntax} *)
module Comp = struct
  include Syncom.Comp

  type kind =
    | Ctype of { location : Location.t }
    | ArrKind of
        { location : Location.t
        ; domain : CLF.Object.t
        ; range : kind
        }
    | PiKind of
        { location : Location.t
        ; parameter_name : Name.t
        ; parameter_type : CLF.Object.t
        ; plicity : Plicity.t
        ; range : kind
        }

  type meta_obj = Location.t * CLF.Object.t

  type meta_typ = CLF.Object.t

  type typ =
    | TypBase of
        { location : Location.t
        ; head : Name.t
        ; spine : meta_obj list
        }
    | TypBox of
        { location : Location.t
        ; typ : meta_typ
        }
    | TypArr of
        { location : Location.t
        ; domain : typ
        ; range : typ
        }
    | TypCross of
        { location : Location.t
        ; typs : typ List2.t
        }
    | TypPiBox of
        { location : Location.t
        ; parameter_name : Name.t
        ; parameter_type : CLF.Object.t
        ; plicity : Plicity.t
        ; range : typ
        }

  and exp =
    | Fn of
        { location : Location.t
        ; parameter_name : Name.t
        ; body : exp
        }
    | Fun of
        { location : Location.t
        ; branches : branch List1.t
        }
    | MLam of
        { location : Location.t
        ; parameter_name : Name.t
        ; body : exp
        }
    | Tuple of
        { location : Location.t
        ; expressions : exp List2.t
        }
    | Let of
        { location : Location.t
        ; pattern : pattern
        ; assignee : exp
        ; body : exp
        }
    | Box of
        { location : Location.t
        ; obj : meta_obj
        }
    | Impossible of
        { location : Location.t
        ; expression : exp
        }
    | Case of
        { location : Location.t
        ; check_exhaustiveness : bool
        ; scrutinee : exp
        ; branches : branch List1.t
        }
    | Hole of
        { location : Location.t
        ; label : string option
        }
    | BoxHole of { location : Location.t }
    | Name of
        { location : Location.t
        ; name : Name.t
        }
    | Apply of
        { location : Location.t
        ; applicand : exp
        ; argument : exp
        }

  and pattern =
    | PatMetaObj of
        { location : Location.t
        ; obj : meta_obj
        }
    | RawPatApplication of
        { location : Location.t
        ; patterns : pattern List1.t
        }
    | PatName of
        { location : Location.t
        ; name : Name.t
        }
    | PatTuple of
        { location : Location.t
        ; patterns : pattern List2.t
        }
    | PatAnn of
        { location : Location.t
        ; pattern : pattern
        ; typ : typ
        }
    | PatMAnn of
        { location : Location.t
        ; pattern : pattern
        ; typs : (Name.t * CLF.Object.t) List1.t
        }
    | PatObs of
        { location : Location.t
        ; name : Name.t
        }

  and branch =
    | Branch of
        { location : Location.t
        ; pattern : pattern
        ; body : exp
        }

  type suffices_typ = typ generic_suffices_typ

  type named_order = Name.t generic_order

  type numeric_order = int generic_order

  type total_dec =
    | NumericTotal of Location.t * numeric_order option
    | NamedTotal of
        Location.t * named_order option * Name.t * Name.t option list
    | Trust of Location.t

  type ctyp_decl = CTypDecl of Name.t * typ

  type mctx = (Identifier.t * CLF.Object.t) List.t

  type gctx = ctyp_decl List.t

  type hypotheses =
    { cD : mctx
    ; cG : gctx
    }

  type proof =
    | Incomplete of Location.t * string option
    | Command of Location.t * command * proof
    | Directive of Location.t * directive

  and command =
    | By of Location.t * exp * Name.t
    | Unbox of Location.t * exp * Name.t * unbox_modifier option

  and directive =
    | Intros of Location.t * hypothetical
    | Solve of Location.t * exp
    | Split of Location.t * exp * split_branch list
    | Suffices of Location.t * exp * (Location.t * typ * proof) list

  and split_branch =
    { case_label : case_label
    ; branch_body : hypothetical
    ; split_branch_loc : Location.t
    }

  and hypothetical =
    { hypotheses : hypotheses
    ; proof : proof
    ; hypothetical_loc : Location.t
    }

  type thm =
    | Program of exp
    | Proof of proof

  let loc_of_exp = function
    | Fn { location; _ }
    | Fun { location; _ }
    | MLam { location; _ }
    | Tuple { location; _ }
    | Let { location; _ }
    | Box { location; _ }
    | Impossible { location; _ }
    | Case { location; _ }
    | Hole { location; _ }
    | BoxHole { location; _ }
    | Name { location; _ }
    | Apply { location; _ } -> location
end

(** {1 Harpoon Command Syntax} *)
module Harpoon = struct
  type defer_kind =
    [ `subgoal
    | `theorem
    ]

  type invoke_kind =
    [ `ih
    | `lemma
    ]

  type level =
    [ `meta
    | `comp
    ]

  type automation_kind =
    [ `auto_intros
    | `auto_solve_trivial
    ]

  type automation_change =
    [ `on
    | `off
    | `toggle
    ]

  type basic_command =
    [ `list
    | `defer
    ]

  type info_kind = [ `prog ]

  type command =
    (* Administrative commands *)
    | Rename of
        { rename_from : Name.t
        ; rename_to : Name.t
        ; level : level
        }
    | ToggleAutomation of automation_kind * automation_change
    | Type of Comp.exp
    | Info of info_kind * Name.t
    | SelectTheorem of Name.t
    | Theorem of
        [ basic_command | `show_ihs | `show_proof | `dump_proof of string ]
    | Session of [ basic_command | `create | `serialize ]
    | Subgoal of basic_command
    | Undo
    | Redo
    | History
    | Translate of Name.t
    (* Actual tactics *)
    | Intros of
        string list option (* list of names for introduced variables *)
    | Split of { scrutinee : Comp.exp }
    | Invert of { scrutinee : Comp.exp }
    | Impossible of { scrutinee : Comp.exp }
    | MSplit of Location.t * Name.t (* split on a metavariable *)
    | Solve of
        Comp.exp (* the expression to solve the current subgoal with *)
    | Unbox of Comp.exp * Name.t * Comp.unbox_modifier option
    | By of Comp.exp * Name.t
    | Suffices of Comp.exp * Comp.suffices_typ list
    | Help
end

module rec Schema : sig
  type t =
    | Identifier of
        { location : Location.t
        ; identifier : Identifier.t
        }
    | Simple of
        { location : Location.t
        ; some : (Identifier.t * CLF.Object.t) List.t
        ; block :
            (Identifier.t Option.t * CLF.Object.t)
            * (Identifier.t * CLF.Object.t) List.t
        }
    | Alternation of
        { location : Location.t
        ; sub_schemas : Schema.t List1.t
        }
end =
  Schema

(** {1 Parser Signature Syntax} *)
module Sgn = struct
  type datatype_flavour =
    | InductiveDatatype
    | StratifiedDatatype

  type precedence = int

  type pragma =
    | NamePrag of
        { constant : Name.t
        ; meta_name : string
        ; comp_name : string option
        }
    | FixPrag of
        { constant : Name.t
        ; fixity : Fixity.t
        ; precedence : precedence
        ; associativity : Associativity.t option
        }
    | NotPrag
    | DefaultAssocPrag of { associativity : Associativity.t }
    | OpenPrag of string list
    | AbbrevPrag of string list * string

  (* Pragmas that need to be declared first *)
  type global_pragma =
    | NoStrengthen
    | Coverage of [ `Error | `Warn ]

  type thm_decl =
    | Theorem of
        { location : Location.t
        ; name : Name.t
        ; typ : Comp.typ
        ; order : Comp.total_dec option
        ; body : Comp.thm
        }

  (** Parsed signature element *)
  type decl =
    | Typ of
        { location : Location.t
        ; identifier : Name.t
        ; kind : LF.Object.t
        }  (** LF type family declaration *)
    | Const of
        { location : Location.t
        ; identifier : Name.t
        ; typ : LF.Object.t
        }  (** LF type constant decalaration *)
    | CompTyp of
        { location : Location.t
        ; identifier : Name.t
        ; kind : Comp.kind
        ; datatype_flavour : datatype_flavour
        }  (** Computation-level data type constant declaration *)
    | CompCotyp of
        { location : Location.t
        ; identifier : Name.t
        ; kind : Comp.kind
        }  (** Computation-level codata type constant declaration *)
    | CompConst of
        { location : Location.t
        ; identifier : Name.t
        ; typ : Comp.typ
        }  (** Computation-level type constructor declaration *)
    | CompDest of
        { location : Location.t
        ; identifier : Name.t
        ; mctx : (Identifier.t * CLF.Object.t) List.t
        ; observation_typ : Comp.typ
        ; return_typ : Comp.typ
        }  (** Computation-level type destructor declaration *)
    | CompTypAbbrev of
        { location : Location.t
        ; identifier : Name.t
        ; kind : Comp.kind
        ; typ : Comp.typ
        }  (** Synonym declaration for computation-level type *)
    | Schema of
        { location : Location.t
        ; identifier : Name.t
        ; schema : Schema.t
        }  (** Declaration of a specification for a set of contexts *)
    | Pragma of
        { location : Location.t
        ; pragma : pragma
        }  (** Compiler directive *)
    | GlobalPragma of
        { location : Location.t
        ; pragma : global_pragma
        }  (** Global directive *)
    | MRecTyp of
        { location : Location.t
        ; declarations : (decl * decl list) List1.t
        }  (** Mutually-recursive LF type family declaration *)
    | Theorems of
        { location : Location.t
        ; theorems : thm_decl List1.t
        }  (** Mutually recursive theorem declaration(s) *)
    | Val of
        { location : Location.t
        ; identifier : Name.t
        ; typ : Comp.typ option
        ; expression : Comp.exp
        }  (** Computation-level value declaration *)
    | Query of
        { location : Location.t
        ; name : Name.t option
        ; mctx : (Identifier.t * CLF.Object.t) List.t
        ; typ : CLF.Object.t
        ; expected_solutions : int option
        ; maximum_tries : int option
        }  (** Logic programming query on LF type *)
    | MQuery of
        { location : Location.t
        ; typ : Comp.typ
        ; expected_solutions : int option
        ; search_tries : int option
        ; search_depth : int option
        }  (** Logic programming mquery on Comp. type *)
    | Module of
        { location : Location.t
        ; identifier : string
        ; declarations : decl list
        }  (** Namespace declaration for other declarations *)
    | Comment of
        { location : Location.t
        ; content : string
        }  (** Documentation comment *)

  (** Parsed Beluga project *)
  type sgn = decl list
end
