(* External Syntax *)

open Support
open Id

(** External LF Syntax *)
module LF = struct
  include Syncom.LF

  type kind =
    | Typ of Location.t
    | ArrKind of Location.t * typ * kind
    | PiKind of Location.t * typ_decl * kind

  and typ_decl =
    | TypDecl of name * typ
    | TypDeclOpt of name

  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of name

  and loc_ctyp = Location.t * ctyp

  and ctyp_decl =
    | Decl of name * loc_ctyp * depend
    | DeclOpt of name

  and typ =
    | Atom of Location.t * name * spine
    | ArrTyp of Location.t * typ * typ
    | PiTyp of Location.t * typ_decl * typ
    | Sigma of Location.t * typ_rec
    | Ctx of Location.t * dctx
    | AtomTerm of Location.t * normal

  and normal =
    | Lam of Location.t * name * normal
    | Root of Location.t * head * spine
    | Tuple of Location.t * tuple
    | LFHole of Location.t * string option
    | Ann of Location.t * normal * typ
    | TList of Location.t * normal list
    | NTyp of Location.t * typ
    | PatEmpty of Location.t

  and head =
    | Name of Location.t * name * sub option
    | Hole of Location.t
    | PVar of Location.t * name * sub option
    | Proj of Location.t * head * proj

  and proj =
    | ByPos of int
    | ByName of name

  and spine =
    | Nil
    | App of Location.t * normal * spine

  and sub_start =
    | EmptySub of Location.t
    | Id of Location.t
    | SVar of Location.t * name * sub option

  and sub = sub_start * normal list

  and typ_rec =
    | SigmaLast of name option * typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and dctx =
    | Null
    | CtxVar of Location.t * name
    | DDec of dctx * typ_decl
    | CtxHole

  and sch_elem =
    | SchElem of Location.t * typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

  and mctx = ctyp_decl ctx

  type mfront =
    | ClObj of dctx * sub
    (* ClObj doesn't *really* contain just a substitution.
       The problem is that syntactically, we can't tell
       whether `[psi |- a]' is a boxed object or
       substitution! So it turns out that,
       syntactically, substitutions encompass both
       possibilities: a substitution beginning with
       EmptySub and having just one normal term in it
       can represent a boxed term. We disambiguate
       substitutions from terms at a later time. *)
    | CObj of dctx

  (** Converts a spine to a list. It is visually "backwards" *)
  let rec list_of_spine : spine -> (Location.t * normal) list =
    function
    | Nil -> []
    | App (l, m, s) -> (l, m) :: list_of_spine s

  let loc_of_normal =
    function
    | Lam (l, _, _) -> l
    | Root (l, _, _) -> l
    | Tuple (l, _) -> l
    | LFHole (l, _) -> l
    | Ann (l, _, _) -> l
    | TList (l, _) -> l
    | NTyp (l, _) -> l
    | PatEmpty l -> l

  let loc_of_head =
    function
    | Name (l, _, _) -> l
    | Hole l -> l
    | PVar (l, _, _) -> l
    | Proj (l, _, _) -> l

  (** Wraps a term into a dummy substitution. *)
  let term tM = (EmptySub (loc_of_normal tM), [tM])
end


(** External Computation Syntax *)
module Comp = struct
  include Syncom.Comp

  type kind =
    | Ctype of Location.t
    | PiKind of Location.t * LF.ctyp_decl * kind

  type meta_obj = Location.t * LF.mfront

  type meta_spine =                             (* Meta-Spine  mS :=         *)
    | MetaNil                                   (* | .                       *)
    | MetaApp of meta_obj * meta_spine          (* | mC mS                   *)

  type meta_typ = LF.loc_ctyp

  type typ =                                           (* Computation-level types *)
    | TypBase of Location.t * name * meta_spine        (*    | c mS               *)
    | TypBox of Location.t * meta_typ                  (*    | [U]                *)
    | TypArr of Location.t * typ * typ                 (*    | tau -> tau         *)
    | TypCross of Location.t * typ * typ               (*    | tau * tau          *)
    | TypPiBox of Location.t * LF.ctyp_decl * typ      (*    | Pi u::U.tau        *)
    | TypInd of typ

  and exp_chk =                                                      (* Computation-level expressions *)
    | Syn        of Location.t * exp_syn                             (*  e ::= i                      *)
    | Fn         of Location.t * name * exp_chk                      (*    | fn x => e                *)
    | Fun        of Location.t * fun_branches                        (*    | fun fbranches            *)
    | MLam       of Location.t * name * exp_chk                      (*    | mlam f => e              *)
    | Pair       of Location.t * exp_chk * exp_chk                   (*    | (e1 , e2)                *)
    | LetPair    of Location.t * exp_syn * (name * name * exp_chk)   (*    | let (x,y) = i in e       *)
    | Let        of Location.t * exp_syn * (name * exp_chk)          (*    | let x = i in e           *)
    | Box        of Location.t * meta_obj                            (*    | [C]                      *)
    | Impossible of Location.t * exp_syn                             (*    | impossible i             *)
    | Case       of Location.t * case_pragma * exp_syn * branch list (*    | case i of branches       *)
    | Hole       of Location.t * string option                       (*    | ?name                    *)
    | BoxHole    of Location.t                                       (*    | _                        *)

  and exp_syn =
    | Name of Location.t * name                          (*  i ::= x/c               *)
    | Apply of Location.t * exp_syn * exp_chk            (*    | i e                 *)
    | BoxVal of Location.t * meta_obj                    (*    | [C]                 *)
    | PairVal of Location.t * exp_syn * exp_syn          (*    | (i , i)             *)
  (* Note that observations are missing.
     In the external syntax, observations are syntactically
     indistinguishable from applications, so we parse them as
     applications. During indexing, they are disambiguated into
     observations.
   *)

  and pattern =
    | PatMetaObj of Location.t * meta_obj
    | PatName of Location.t * name * pattern_spine
    | PatPair of Location.t * pattern * pattern
    | PatAnn of Location.t * pattern * typ

  and pattern_spine =
    | PatNil of Location.t
    | PatApp of Location.t * pattern * pattern_spine
    | PatObs of Location.t * name * pattern_spine

  and branch =
    | Branch of Location.t *  LF.ctyp_decl LF.ctx  * pattern * exp_chk

  and fun_branches =
    | NilFBranch of Location.t
    | ConsFBranch of Location.t * (pattern_spine * exp_chk) * fun_branches

  (* the definition of branch_pattern will be removed and replaced by the more general notion of patterns;
     it remains currently so we can still use the old parser without modifications -bp *)
  and branch_pattern =
    | NormalPattern of LF.normal * exp_chk
    | EmptyPattern

  type suffices_typ = typ generic_suffices_typ

  type named_order = name generic_order
  type numeric_order = int generic_order

  type total_dec =
    | NumericTotal of Location.t * numeric_order option
    | NamedTotal of Location.t * named_order option * name * name option list
    | Trust of Location.t

  type ctyp_decl =
    | CTypDecl of name * typ

  type gctx = ctyp_decl LF.ctx

  type hypotheses =
    { cD : LF.mctx
    ; cG : gctx
    }

  type proof =
    | Incomplete of Location.t * string option
    | Command of Location.t * command * proof
    | Directive of Location.t * directive

  and command =
    | By of Location.t * exp_syn * name
    | Unbox of Location.t * exp_syn * name * unbox_modifier option

  and directive =
    | Intros of Location.t * hypothetical
    | Solve of Location.t * exp_chk
    | Split of Location.t * exp_syn * split_branch list
    | Suffices of Location.t * exp_syn * (Location.t * typ * proof) list

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
    | Program of exp_chk
    | Proof of proof
end

(** Syntax of Harpoon commands. *)
module Harpoon = struct
  include Syncom.Harpoon

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

  type info_kind =
    [ `prog
    ]

  type command =
    (* Administrative commands *)
    | Rename
      of name (* from *)
         * name (* to *)
         * level
    | ToggleAutomation of automation_kind * automation_change

    | Type of Comp.exp_syn
    | Info of info_kind * Id.name
    | SelectTheorem of Id.name
    | Theorem of [ basic_command | `show_ihs | `show_proof | `dump_proof of string ]
    | Session of [ basic_command | `create | `serialize ]
    | Subgoal of basic_command
    | Undo
    | Redo
    | History

    | Translate of Id.name

    (* Actual tactics *)
    | Intros of string list option (* list of names for introduced variables *)

    | Split of split_kind * Comp.exp_syn (* the expression to split on *)
    | MSplit of Location.t * Id.name (* split on a metavariable *)
    | Solve of Comp.exp_chk (* the expression to solve the current subgoal with *)
    | Unbox of Comp.exp_syn * Id.name * Comp.unbox_modifier option
    | By of Comp.exp_syn * Id.name
    | Suffices of Comp.exp_syn * Comp.suffices_typ list
    | Help
end


(** External Signature Syntax *)
module Sgn = struct

  type datatype_flavour =
    | InductiveDatatype
    | StratifiedDatatype

  type assoc = Left | Right | None
  type precedence = int
  type fix = Prefix | Postfix | Infix

  type pragma =
    | OptsPrag          of string list
    | NamePrag          of name * string * string option
    | FixPrag           of name * fix * precedence * assoc option
    | NotPrag
    | DefaultAssocPrag  of assoc
    | OpenPrag          of string list
    | AbbrevPrag        of string list * string

  (* Pragmas that need to be declared first *)
  type global_pragma =
    | NoStrengthen
    | Coverage of [`Error | `Warn]

  type thm_decl =
    { thm_loc : Location.t
    ; thm_name : name
    ; thm_typ : Comp.typ
    ; thm_order : Comp.total_dec option
    ; thm_body : Comp.thm
    }

  (** Parsed signature element *)
  type decl =
    | Typ of
      { location: Location.t
      ; identifier: name
      ; kind: LF.kind
      } (** LF type family declaration *)

    | Const of
      { location: Location.t
      ; identifier: name
      ; typ: LF.typ
      } (** LF type constant decalaration *)

    | CompTyp of
      { location: Location.t
      ; identifier: name
      ; kind: Comp.kind
      ; datatype_flavour: datatype_flavour
      } (** Computation-level data type constant declaration *)

    | CompCotyp of
      { location: Location.t
      ; identifier: name
      ; kind: Comp.kind
      } (** Computation-level codata type constant declaration *)

    | CompConst of
      { location: Location.t
      ; identifier: name
      ; typ: Comp.typ
      } (** Computation-level type constructor declaration *)

    | CompDest of
      { location: Location.t
      ; identifier: name
      ; mctx: LF.mctx
      ; observation_typ: Comp.typ
      ; return_typ: Comp.typ
      } (** Computation-level type destructor declaration *)

    | CompTypAbbrev of
      { location: Location.t
      ; identifier: name
      ; kind: Comp.kind
      ; typ: Comp.typ
      } (** Synonym declaration for computation-level type *)

    | Schema of
      { location: Location.t
      ; identifier: name
      ; schema: LF.schema
      } (** Declaration of a specification for a set of contexts *)

    | Pragma of
      { location: Location.t
      ; pragma: pragma
      } (** Compiler directive *)

    | GlobalPragma of
      { location: Location.t
      ; pragma: global_pragma
      } (** Global directive *)

    | MRecTyp of
      { location: Location.t
      ; declarations: (decl * decl list) Nonempty.t
      } (** Mutually-recursive LF type family declaration *)

    | Theorem of
      { location: Location.t
      ; theorems: thm_decl list
      } (** Mutually recursive theorem declaration(s) *)

    | Val of
      { location: Location.t
      ; identifier: name
      ; typ: Comp.typ option
      ; expression: Comp.exp_syn
      } (** Computation-level value declaration *)

    | Query of
      { location: Location.t
      ; name: name option
      ; typ: LF.typ
      ; expected_solutions: int option
      ; maximum_tries: int option
      } (** Logic programming query on LF type *)

    | Module of
      { location: Location.t
      ; identifier: string
      ; declarations: decl list
      } (** Namespace declaration for other declarations *)

    | Comment of
      { location: Location.t
      ; content: string
      } (** Documentation comment *)

  (** Parsed Beluga project *)
  type sgn = decl list

end
