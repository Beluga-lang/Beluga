(** External Syntax *)
(** External LF Syntax *)
open Id
open Pragma

module Loc = Camlp4.PreCast.Loc

module LF = struct

  type kind =
    | Typ     of Loc.t
    | ArrKind of Loc.t * typ      * kind
    | PiKind  of Loc.t * typ_decl * kind

  and typ_decl =
    | TypDecl of name * typ
(*      | TypDeclOpt of name  *)

  and ctyp_decl =
    | MDecl of Loc.t * name * typ  * dctx
    | PDecl of Loc.t * name * typ  * dctx
    | SDecl of Loc.t * name * dctx * dctx
    | CDecl of Loc.t * name * name

  and typ =
    | Atom   of Loc.t * name * spine
    | ArrTyp of Loc.t * typ      * typ
    | PiTyp  of Loc.t * typ_decl * typ
    | Sigma of Loc.t * typ_rec
    | Ctx   of Loc.t * dctx

  and normal =
    | Lam  of Loc.t * name * normal
    | Root of Loc.t * head * spine
    | Tuple of Loc.t * tuple
    | Ann of Loc.t * normal * typ

  and head =
    | Name  of Loc.t * name
    | MVar  of Loc.t * name * sub
    | Hole  of Loc.t
    | PVar  of Loc.t * name * sub
    | ProjName  of Loc.t * int * name
    | ProjPVar  of Loc.t * int * (name * sub)

  and spine =
    | Nil
    | App of Loc.t * normal * spine

  and sub =
    | EmptySub of Loc.t
    | Dot      of Loc.t * sub * front
    | Id       of Loc.t
    | SVar     of Loc.t * name * sub  (* this needs to be be then turned into a subst. *)

  and front =
    | Head     of head
    | Normal   of normal

  and typ_rec =
    | SigmaLast of typ
    | SigmaElem of name * typ * typ_rec

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and dctx =
    | Null
    | CtxVar   of Loc.t * name
    | DDec     of dctx * typ_decl

  and 'a ctx =
    | Empty
    | Dec of 'a ctx * 'a

  and sch_elem =
    | SchElem of Loc.t * typ_decl ctx * typ_rec

  and schema =
    | Schema of sch_elem list

  and psi_hat  = name list

  and mctx = ctyp_decl ctx

end


(** External Computation Syntax *)
module Comp = struct

 type depend =
   | Implicit
   | Explicit

 type meta_obj =
   | MetaCtx of Loc.t * LF.dctx
   | MetaObj of Loc.t * LF.psi_hat * LF.normal
   | MetaObjAnn of Loc.t * LF.dctx * LF.normal
   | MetaParam of Loc.t * LF.psi_hat * LF.head
   | MetaSObj of Loc.t * LF.psi_hat * LF.sub
   | MetaSObjAnn of Loc.t * LF.dctx * LF.sub

 type meta_spine =
   | MetaNil
   | MetaApp of meta_obj * meta_spine


 type meta_typ =
   | MetaSchema of Loc.t * name
   | MetaTyp of Loc.t * LF.typ * LF.dctx
   | MetaParamTyp of Loc.t  * LF.typ * LF.dctx
   | MetaSubTyp  of Loc.t * LF.dctx * LF.dctx

 type mabstr = CObj | MObj | PObj | SObj

 type typ =                                     (* Computation-level types *)
   | TypBase of Loc.t * name * meta_spine
   | TypBox  of Loc.t * meta_typ
   | TypArr   of Loc.t * typ * typ              (*    | tau -> tau         *)
   | TypCross of Loc.t * typ * typ              (*    | tau * tau          *)
   | TypPiBox of Loc.t * (LF.ctyp_decl * depend) * typ
                                                (*     | Pi u::U.tau       *)
   | TypBool                                    (*     | Bool              *)

  and exp_chk =                            (* Computation-level expressions *)
     | Syn    of Loc.t * exp_syn                (*  e ::= i                 *)
     | Fun    of Loc.t * name * exp_chk         (*    | fn f => e           *)
     | Cofun  of Loc.t * (copattern_spine * exp_chk) list  (*    | (cofun hd => e | tl => e') *)
     | MLam   of Loc.t * (name * mabstr) * exp_chk  (*| mlam f => e         *)
     | Pair   of Loc.t * exp_chk * exp_chk      (*    | (e1 , e2)           *)
     | LetPair of Loc.t * exp_syn * (name * name * exp_chk)
                                                (*    | let (x,y) = i in e  *)
     | Let    of Loc.t * exp_syn * (name * exp_chk)
                                                (*    | let x = i in e      *)
     | Box of Loc.t * meta_obj
     | Case   of Loc.t * case_pragma * exp_syn * branch list  (*    | case i of branches   *)
     | If of Loc.t * exp_syn * exp_chk * exp_chk(*    | if i then e1 else e2 *)
     | Hole of Loc.t				(*    | ?                   *)

  and exp_syn =
     | Var    of Loc.t * name                   (*  i ::= x                 *)
     | DataConst  of Loc.t * name               (*    | c                   *)
     | Const  of Loc.t * name                   (*    | c                   *)
     | Apply  of Loc.t * exp_syn * exp_chk      (*    | i e                 *)
     | MApp of Loc.t * exp_syn * meta_obj       (*    | i [C]               *)
     | BoxVal of Loc.t * LF.dctx * LF.normal
     | PairVal of Loc.t * exp_syn * exp_syn
     | Ann    of Loc.t * exp_chk * typ          (*    | e : tau             *)
     | Equal  of Loc.t * exp_syn * exp_syn
     | Boolean of Loc.t * bool

 and pattern =
   | PatEmpty  of Loc.t * LF.dctx
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

  and branch =
    | EmptyBranch of Loc.t *  LF.ctyp_decl LF.ctx  * pattern
    | Branch of Loc.t *  LF.ctyp_decl LF.ctx  * pattern * exp_chk
    (* The following two are from the old implementation and will be removed eventually;
       and replaced by the more general notion of patterns and branches above;
       it remains currently so we can still use the old parser without modifications
       -bp *)
    | BranchBox of Loc.t *  LF.ctyp_decl LF.ctx
        * (LF.dctx * branch_pattern * (LF.typ * LF.dctx) option)

    | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx
        * (LF.dctx * LF.sub * LF.dctx option)
        * exp_chk

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

 type  kind =
   | Ctype of Loc.t
(*     | ArrKind of Loc.t * meta_typ  * kind *)
   | PiKind  of Loc.t * (LF.ctyp_decl * depend) * kind


 (* Useful for debugging the parser, but there should be a better place for them... *)
 let rec synToString = function
     | Var    (_loc,  _) -> "Var"
     | Apply  (_loc,  syn, chk) -> "Apply(" ^ synToString syn ^ ", " ^ chkToString chk ^ ")"
(*     | CtxApp (_loc,  syn, _dctx) -> "CtxApp(" ^ synToString syn ^ ", _dctx)" *)
     | MApp   (_loc,  syn, _) -> "MApp(" ^ synToString syn ^ ", ...)"
     | BoxVal (_loc, _, _) -> "BoxVal(...)"
     | Ann    (_loc, chk, _) -> "Ann(" ^ chkToString chk ^ ", _)"
     | Equal   (_loc,  syn1, syn2) -> "Equal("  ^ synToString syn1 ^ " == " ^ synToString syn2 ^ ")"
     | Boolean (_loc, _) -> "Boolean(_)"

 and chkToString = function
     | Syn     (_loc,  syn) -> "Syn(" ^ synToString syn ^ ")"
     | Fun     (_loc, _, chk) -> "Fun(_, " ^ chkToString chk ^ ")"
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
  type positivity_flag = 
    | Positivity
    | Stratify of Loc.t * (string  option)
    (* | Stratify of Loc.t * Comp.order * name * (name option) list  *)

  type pragma =
    | OptsPrag of string list
    | NamePrag of name * string * string option
    | NotPrag

  type decl =
    | Const    of Loc.t * name * LF.typ
    | Typ      of Loc.t * name * LF.kind
    | CompTyp  of Loc.t * name * Comp.kind  * positivity_flag option
    | CompCotyp of Loc.t * name * Comp.kind
    | CompConst of Loc.t * name * Comp.typ
    | CompDest of Loc.t * name * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema   of Loc.t * name * LF.schema
    | Pragma   of Loc.t * pragma
    | MRecTyp  of Loc.t * decl list list
    | Rec      of Loc.t * Comp.rec_fun list
    | Val      of Loc.t * name * Comp.typ option * Comp.exp_syn
    | Query    of Loc.t * name option * LF.typ * int option * int option

  type sgn = decl list

end
