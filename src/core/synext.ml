(* External Syntax *)

open Id

module Loc = Location

(** External LF Syntax *)
module LF = struct
  include Syncom.LF

  type kind =
    | Typ     of Loc.t
    | ArrKind of Loc.t * typ      * kind
    | PiKind  of Loc.t * typ_decl * kind

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

  and loc_ctyp = Loc.t * ctyp

  and ctyp_decl =
    | Decl of name * loc_ctyp * depend
    | DeclOpt of name

  and typ =
    | Atom   of Loc.t * name * spine
    | ArrTyp of Loc.t * typ      * typ
    | PiTyp  of Loc.t * typ_decl * typ
    | Sigma of Loc.t * typ_rec
    | Ctx   of Loc.t * dctx
    | AtomTerm of Loc.t * normal

  and normal =
    | Lam  of Loc.t * name * normal
    | Root of Loc.t * head * spine
    | Tuple of Loc.t * tuple
    | LFHole of Loc.t * string option
    | Ann of Loc.t * normal * typ
    | TList of Loc.t * normal list
    | NTyp of Loc.t * typ
    | PatEmpty  of Loc.t

  and head =
    | Name  of Loc.t * name * sub option
    | Hole  of Loc.t
    | PVar  of Loc.t * name * sub option
    | Proj  of Loc.t * head * proj

  and proj =
    | ByPos of int
    | ByName of name

  and spine =
    | Nil
    | App of Loc.t * normal * spine

  and sub_start =
    | EmptySub of Loc.t
    | Id of Loc.t
    | SVar of Loc.t * name * sub option

  and sub = sub_start * normal list

  and typ_rec =
    | SigmaLast of name option * typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and dctx =
    | Null
    | CtxVar   of Loc.t * name
    | DDec     of dctx * typ_decl
    | CtxHole

  and sch_elem =
    | SchElem of Loc.t * typ_decl ctx * typ_rec

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
  let rec list_of_spine (sp : spine) : (Loc.t * normal) list =
    match sp with
    | Nil -> []
    | App (l, m, s) -> (l, m) :: list_of_spine s

  let loc_of_normal = function
    | Lam (l, _, _) -> l
    | Root (l, _, _) -> l
    | Tuple (l, _) -> l
    | LFHole (l, _) -> l
    | Ann (l, _, _) -> l
    | TList (l, _) -> l
    | NTyp (l, _) -> l
    | PatEmpty l -> l

  let loc_of_head = function
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
   | Ctype of Loc.t
   | PiKind  of Loc.t * LF.ctyp_decl * kind

 type meta_obj = Loc.t * LF.mfront

 type meta_spine =                             (* Meta-Spine  mS :=         *)
   | MetaNil                                   (* | .                       *)
   | MetaApp of meta_obj * meta_spine          (* | mC mS                   *)

 type meta_typ = LF.loc_ctyp

 type typ =                                           (* Computation-level types *)
   | TypBase of Loc.t * name * meta_spine             (*    | c mS               *)
   | TypBox  of Loc.t * meta_typ                      (*    | [U]                *)
   | TypArr   of Loc.t * typ * typ                    (*    | tau -> tau         *)
   | TypCross of Loc.t * typ * typ                    (*    | tau * tau          *)
   | TypPiBox of Loc.t * LF.ctyp_decl * typ           (*    | Pi u::U.tau        *)
   | TypInd of typ

 and exp_chk =                                 (* Computation-level expressions *)
   | Syn        of Loc.t * exp_syn                           (*  e ::= i                 *)
   | Fn         of Loc.t * name * exp_chk                    (*    | fn x => e           *)
   | Fun        of Loc.t * fun_branches                      (*    | fun fbranches       *)
   | MLam       of Loc.t * name * exp_chk                    (*    | mlam f => e         *)
   | Pair       of Loc.t * exp_chk * exp_chk                 (*    | (e1 , e2)           *)
   | LetPair    of Loc.t * exp_syn * (name * name * exp_chk) (*    | let (x,y) = i in e  *)
   | Let        of Loc.t * exp_syn * (name * exp_chk)        (*    | let x = i in e      *)
   | Box        of Loc.t * meta_obj                          (*    | [C]                 *)
   | Impossible of Loc.t * exp_syn                           (*    | impossible i        *)
   | Case       of Loc.t * case_pragma * exp_syn * branch list  (*    | case i of branches *)
   | Hole       of Loc.t * string option     				         (*    | ?name               *)

 and exp_syn =
   | Name   of Loc.t * name                        (*  i ::= x/c               *)
   | Apply  of Loc.t * exp_syn * exp_chk           (*    | i e                 *)
   | BoxVal of Loc.t * meta_obj                    (*    | [C]                 *)
   | PairVal of Loc.t * exp_syn * exp_syn          (*    | (i , i)             *)
  (* Note that observations are missing.
     In the external syntax, observations are syntactically
     indistinguishable from applications, so we parse them as
     applications. During indexing, they are disambiguated into
     observations.
   *)

 and pattern =
   | PatMetaObj of Loc.t * meta_obj
   | PatName   of Loc.t * name * pattern_spine
   | PatPair  of Loc.t * pattern * pattern
   | PatAnn   of Loc.t * pattern * typ

 and pattern_spine =
   | PatNil of Loc.t
   | PatApp of Loc.t * pattern * pattern_spine
   | PatObs of Loc.t * name * pattern_spine

 and branch =
   | Branch of Loc.t *  LF.ctyp_decl LF.ctx  * pattern * exp_chk

 and fun_branches =
   | NilFBranch of Loc.t
   | ConsFBranch of Loc.t * (pattern_spine * exp_chk) * fun_branches

  (* the definition of branch_pattern will be removed and replaced by the more general notion of patterns;
     it remains currently so we can still use the old parser without modifications -bp *)
  and branch_pattern =
     | NormalPattern of LF.normal * exp_chk
     | EmptyPattern

 type 'a order' =
   | Arg of 'a			(* O ::= x                    *)
   | Lex of 'a order' list                 (*     | {O1 .. On}           *)
   | Simul of 'a order' list               (*     | [O1 .. On]           *)
 (* Note: Simul is currently unused. It doesn't even have a parser. -je *)

 let rec map_order (f : 'a -> 'b) : 'a order' -> 'b order' =
   function
   | Arg x -> Arg (f x)
   | Lex xs -> Lex (List.map (map_order f) xs)
   | Simul xs -> Simul (List.map (map_order f) xs)

 type order = name order'
 type numeric_order = int order'

 type total_dec =
   | Total of Loc.t * order option * name * (name option) list
	 | Trust of Loc.t

 type ctyp_decl =
   | CTypDecl of name * typ

 type gctx = ctyp_decl LF.ctx

 type context_case = LF.typ generic_context_case
 type case_label = context_case generic_case_label

 type hypotheses =
   { cD : LF.mctx
   ; cG : gctx
   }

 type proof =
   | Incomplete of Loc.t * string option
   | Command of Loc.t * command * proof
   | Directive of Loc.t * directive

 and command =
   | By of Loc.t * Syncom.Harpoon.invoke_kind * exp_syn * name * boxity
   | Unbox of Loc.t * exp_syn * name

 and directive =
   | Intros of Loc.t * hypothetical
   | Solve of Loc.t * exp_chk
   | Split of Loc.t * exp_syn * split_branch list

 and split_branch =
   { case_label : case_label
   ; branch_body : hypothetical
   ; split_branch_loc : Loc.t
   }

 and hypothetical =
   { hypotheses : hypotheses
   ; proof : proof
   ; hypothetical_loc : Loc.t
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

  type command =
    (* Administrative commands *)

    | Rename of name (* from *)
                * name (* to *)
                * level
    | ToggleAutomation of automation_kind * automation_change

    | Type of Comp.exp_syn
    | Theorem of [ basic_command | `select of Id.name | `show_ihs | `show_proof ]
    | Session of [ basic_command | `select of Id.name | `create of Id.name ]
    | Subgoal of basic_command

    (* Actual tactics *)
    | Intros of string list option (* list of names for introduced variables *)

    | Split of split_kind * Comp.exp_syn (* the expression to split on *)
    | MSplit of Loc.t * Id.name (* split on a metavariable *)
    | Solve of Comp.exp_chk (* the expression to solve the current subgoal with *)
    | Unbox of Comp.exp_syn * Id.name
    | By of Comp.exp_syn * Id.name * Comp.boxity
    | Suffices of Comp.exp_syn * Comp.typ list
end


(** External Signature Syntax *)
module Sgn = struct

  type datatype_flavour =
      InductiveDatatype
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
    | Coverage     of [`Error | `Warn]

  type thm_decl =
    { thm_loc : Loc.t
    ; thm_name : name
    ; thm_typ : Comp.typ
    ; thm_order : Comp.total_dec option
    ; thm_body : Comp.thm
    }

  type decl =
    | Const         of Loc.t * name * LF.typ
    | Typ           of Loc.t * name * LF.kind
    | CompTyp       of Loc.t * name * Comp.kind  * datatype_flavour
    | CompCotyp     of Loc.t * name * Comp.kind
    | CompConst     of Loc.t * name * Comp.typ
    | CompDest      of Loc.t * name * LF.mctx * Comp.typ * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema        of Loc.t * name * LF.schema
    | Pragma        of Loc.t * pragma
    | GlobalPragma  of Loc.t * global_pragma
    | MRecTyp       of Loc.t * (decl * decl list) list
    | Theorem       of Loc.t * thm_decl list
    | Val           of Loc.t * name * Comp.typ option * Comp.exp_syn
    | Query         of Loc.t * name option * LF.typ * int option * int option
    | Module        of Loc.t * string * decl list
    | Comment of Loc.t * string
  type sgn = decl list
end
