(** External Syntax *)
(** External LF Syntax *)
open Id
open Pragma

module Loc = Camlp4.PreCast.Loc

module LF = struct
  
  type depend =
    | Maybe
    | No
    | Inductive

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

  and svar_class = 
    | Ren
    | Subst

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
    | LFHole of Loc.t
    | Ann of Loc.t * normal * typ
    | TList of Loc.t * normal list
    | NTyp of Loc.t * typ
    | PatEmpty  of Loc.t

  and head =
    | Name  of Loc.t * name
    | MVar  of Loc.t * name * sub
    | Hole  of Loc.t
    | PVar  of Loc.t * name * sub
    | Proj  of Loc.t * head * proj

  and proj = 
    | ByPos of int
    | ByName of name

  and spine =
    | Nil
    | App of Loc.t * normal * spine

  and sub =
    | EmptySub of Loc.t
    | Dot      of Loc.t * sub * front
    | Id       of Loc.t
    | RealId
    | SVar     of Loc.t * name * sub  (* this needs to be be then turned into a subst. *)

  and front =
    | Head     of head
    | Normal   of normal

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

  and 'a ctx =
    | Empty
    | Dec of 'a ctx * 'a

  and sch_elem =
    | SchElem of Loc.t * typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

  and mctx = ctyp_decl ctx

end


(** External Computation Syntax *)
module Comp = struct

 type kind =
   | Ctype of Loc.t
   | PiKind  of Loc.t * LF.ctyp_decl * kind

 type clobj = 
   | MObj of LF.normal
   | SObj of LF.sub
   | PObj of LF.head

 type mfront =
   | ClObj of LF.dctx * clobj
   | CObj of LF.dctx

 type meta_obj = Loc.t * mfront

 type meta_spine =                             (* Meta-Spine  mS :=         *)
   | MetaNil                                   (* | .                       *) 
   | MetaApp of meta_obj * meta_spine          (* | mC mS                   *)

 type meta_typ = LF.loc_ctyp

 type typ =                                     (* Computation-level types *)
   | TypBase of Loc.t * name * meta_spine       (*    | c mS               *)
   | TypBool                                    (*    | Bool               *)
   | TypBox  of Loc.t * meta_typ                (*    | [U]                *) 
   | TypArr   of Loc.t * typ * typ              (*    | tau -> tau         *)
   | TypCross of Loc.t * typ * typ              (*    | tau * tau          *) 
   | TypPiBox of Loc.t * LF.ctyp_decl * typ     (*     | Pi u::U.tau       *)
   | TypInd of typ 

  and exp_chk =                                 (* Computation-level expressions *)
     | Syn    of Loc.t * exp_syn                     (*  e ::= i                 *)
     | Fn     of Loc.t * name * exp_chk              (*    | fn x => e           *) 
     | Fun    of Loc.t * fun_branches                (*    | fun fbranches       *)
     | Cofun  of Loc.t * (copattern_spine * exp_chk) list  (*    | (cofun hd => e | tl => e') *)
     | MLam   of Loc.t * name * exp_chk              (*| mlam f => e         *)
     | Pair   of Loc.t * exp_chk * exp_chk           (*    | (e1 , e2)           *)
     | LetPair of Loc.t * exp_syn * (name * name * exp_chk)
                                                     (*    | let (x,y) = i in e  *)
     | Let    of Loc.t * exp_syn * (name * exp_chk)  (*    | let x = i in e      *)          
     | Box of Loc.t * meta_obj
     | Case   of Loc.t * case_pragma * exp_syn * branch list  (*    | case i of branches   *)
     | If of Loc.t * exp_syn * exp_chk * exp_chk     (*    | if i then e1 else e2 *)
     | Hole of Loc.t				     (*    | ?                   *)

  and exp_syn =
     | Var    of Loc.t * name                        (*  i ::= x                 *)
     | DataConst  of Loc.t * name                    (*    | c                   *)
     | Obs    of Loc.t * exp_chk * name              (*    | e.d                 *)
     | Const  of Loc.t * name                        (*    | c                   *)
     | Apply  of Loc.t * exp_syn * exp_chk           (*    | i e                 *)
     | BoxVal of Loc.t * meta_obj
     | PairVal of Loc.t * exp_syn * exp_syn
     | Ann    of Loc.t * exp_chk * typ               (*    | e : tau             *)
     | Equal  of Loc.t * exp_syn * exp_syn
     | Boolean of Loc.t * bool

 and pattern =
   | PatMetaObj of Loc.t * meta_obj
   | PatConst of Loc.t * name * pattern_spine
   | PatVar   of Loc.t * name
   | PatPair  of Loc.t * pattern * pattern
   | PatTrue  of Loc.t
   | PatFalse of Loc.t
   | PatAnn   of Loc.t * pattern * typ

 and pattern_spine =
   | PatNil of Loc.t
   | PatApp of Loc.t * pattern * pattern_spine
   | PatObs of Loc.t * name * pattern_spine

 and branch =
   | EmptyBranch of Loc.t *  LF.ctyp_decl LF.ctx  * pattern
   | Branch of Loc.t *  LF.ctyp_decl LF.ctx  * pattern * exp_chk

 and fun_branches =
   | NilFBranch of Loc.t
   | ConsFBranch of Loc.t * (pattern_spine * exp_chk) * fun_branches 
       
  (* the definition of branch_pattern will be removed and replaced by the more general notion of patterns;
     it remains currently so we can still use the old parser without modifications -bp *)
  and branch_pattern =
     | NormalPattern of LF.normal * exp_chk
     | EmptyPattern

  and copattern_spine =
    | CopatNil of Loc.t
    | CopatApp of Loc.t * name * copattern_spine
    | CopatMeta of Loc.t * meta_obj * copattern_spine

 type order =
      Arg of name			(* O ::= x                    *)
    | Lex of order list                 (*     | {O1 .. On}           *)
    | Simul of order list               (*     | [O1 .. On]           *)

 type total_dec = Total of Loc.t * order option * name * (name option) list
		  | Trust of Loc.t

 type rec_fun = RecFun of Loc.t * name * total_dec option * typ * exp_chk

 (* Useful for debugging the parser, but there should be a better place for them... *)
 let rec synToString = function
     | Var    (_loc,  _) -> "Var"
     | Apply  (_loc,  syn, chk) -> "Apply(" ^ synToString syn ^ ", " ^ chkToString chk ^ ")"
(*     | CtxApp (_loc,  syn, _dctx) -> "CtxApp(" ^ synToString syn ^ ", _dctx)" *)
     | BoxVal (_loc, _) -> "BoxVal(...)"
     | Ann    (_loc, chk, _) -> "Ann(" ^ chkToString chk ^ ", _)"
     | Equal   (_loc,  syn1, syn2) -> "Equal("  ^ synToString syn1 ^ " == " ^ synToString syn2 ^ ")"
     | Boolean (_loc, _) -> "Boolean(_)"

 and chkToString = function
     | Syn     (_loc,  syn) -> "Syn(" ^ synToString syn ^ ")"
     | Fn     (_loc, _, chk) -> "Fn(_, " ^ chkToString chk ^ ")"
     | MLam    (_loc, _, chk) ->  "MLam(_, " ^ chkToString chk ^ ")"
     | Pair    (_loc, chk1, chk2) ->  "Fun(_, " ^ chkToString chk1 ^ ", " ^ chkToString chk2 ^ ")"
     | LetPair (_loc, syn, (_, _, chk)) -> "LetPair(" ^ synToString syn ^",  (_, _, " ^ chkToString chk ^ "))"
     | Let (_loc, syn, (_, chk)) -> "Let(" ^ synToString syn ^",  (_, " ^ chkToString chk ^ "))"
     | Box     (_loc, _) -> "Box(...)"
     | Case    (_loc, _, syn, _) -> "Case(" ^ synToString syn ^ " of ...)"
     | If      (_loc, syn, chk1, chk2) -> "If(" ^ synToString syn ^ " Then " ^  chkToString chk1 ^ " Else " ^ chkToString chk2 ^ ")"
     | Hole    (_loc) -> "Hole"

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
    | Rec           of Loc.t * Comp.rec_fun list
    | Val           of Loc.t * name * Comp.typ option * Comp.exp_syn
    | Query         of Loc.t * name option * LF.typ * int option * int option
    | Module        of Loc.t * string * decl list
    | Comment of Loc.t * string
  type sgn = decl list



end
