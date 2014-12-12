(** Internal Syntax *)
(** Internal LF Syntax *)
open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

module LF = struct

  type depend =
    | No      (* Explicit *)
    | Maybe   (* Implicit *)

  type kind =
    | Typ
    | PiKind of (typ_decl * depend) * kind

  and typ_decl =                              (* LF Declarations                *)
    | TypDecl of name * typ                   (* D := x:A                       *)
    | TypDeclOpt of name                      (*   |  x:_                       *)

  and ctyp =
    | MTyp of typ * dctx * depend
    | PTyp of typ * dctx * depend
    | STyp of dctx * dctx * depend
    | CTyp of cid_schema * depend

  and ctyp_decl =                             (* Contextual Declarations        *)
    | Decl of name * ctyp
    | DeclOpt of name
                                              (* Potentially, A is Sigma type? *)

  and typ =                                   (* LF level                       *)
    | Atom  of Loc.t * cid_typ * spine        (* A ::= a M1 ... Mn              *)
    | PiTyp of (typ_decl * depend) * typ      (*   | Pi x:A.B                   *)
    | Sigma of typ_rec
    | TClo  of (typ * sub)                    (*   | TClo(A,s)                  *)


  and normal =                                (* normal terms                   *)
    | Lam  of Loc.t * name * normal           (* M ::= \x.M                     *)
    | Root of Loc.t * head * spine            (*   | h . S                      *)
    | LFHole of Loc.t
    | Clo  of (normal * sub)                  (*   | Clo(N,s)                   *)
    | Tuple of Loc.t * tuple

  and head =
    | BVar  of offset                         (* H ::= x                        *)
    | Const of cid_term                       (*   | c                          *)
    | MMVar of mm_var * (msub * sub)          (*   | u[t ; s]                   *)
    | MPVar of mm_var * (msub * sub)          (*   | p[t ; s]                   *)
    | MVar  of cvar * sub                     (*   | u[s]                       *)
    | PVar  of offset * sub                   (*   | p[s]                       *)
    | AnnH  of head * typ                     (*   | (H:A)                      *)
    | Proj  of head * int                     (*   | x.k | #p.k s               *)

    | FVar  of name                           (* free variable for type
                                                 reconstruction                 *)
    | FMVar of name * sub                     (* free meta-variable for type
                                                 reconstruction                 *)
    | FPVar of name * sub                     (* free parameter variable for type
                                                 reconstruction                 *)
    | HClo  of offset * offset * sub            (*   | HClo(x, #S[sigma])         *)
    | HMClo of offset * mm_var * (msub * sub) (*   | HMClo(x, #S[theta;sigma])  *)

  and spine =                                 (* spine                          *)
    | Nil                                     (* S ::= Nil                      *)
    | App  of normal * spine                  (*   | M . S                      *)
    | SClo of (spine * sub)                   (*   | SClo(S,s)                  *)

  and sub =                                   (* Substitutions                  *)
    | Shift of offset                         (* sigma ::= ^(psi,n)             *)
    | SVar  of offset * int * sub           (*   | s[sigma]                   *)
    | FSVar of name *  offset * sub           (*   | s[sigma]                   *)
    | Dot   of front * sub                    (*   | Ft . s                     *)
    | MSVar of mm_var * offset * (msub * sub) (*   | u[t ; s]                   *)
    | EmptySub
    | Undefs

  and front =                                 (* Fronts:                        *)
    | Head of head                            (* Ft ::= H                       *)
    | Obj  of normal                          (*    | N                         *)
    | Undef                                   (*    | _                         *)

                                             (* Contextual substitutions       *)
 and mfront =                                (* Fronts:                        *)
   | MObj of psi_hat * normal                (* Mft::= Psihat.N                *)
   | PObj of psi_hat * head                  (*    | Psihat.p[s] | Psihat.x    *)
   | SObj of psi_hat * sub
   | CObj of dctx                            (*    | Psi                       *)
   | MV   of offset                          (*    | u//u | p//p | psi/psi     *)
   | MUndef

 and msub =                                  (* Contextual substitutions       *)
   | MShift of int                           (* theta ::= ^n                   *)
   | MDot   of mfront * msub                 (*       | MFt . theta            *)

 and csub =                                  (* Context substitutions          *)
   | CShift of int                           (* delta ::= ^n                   *)
   | CDot   of dctx * csub                   (*       | cPsi .delta            *)

  and cvar =                                  (* Contextual Variables           *)
    | Offset of offset                        (* Bound Variables                *)
    | Inst   of name * normal option ref * dctx * typ * cnstr list ref * depend
       (* D ; Psi |- M <= A provided constraint *)

  and mm_var  =                               (* Meta^2 Variables                *)
    | MInst   of name * normal option ref * mctx * dctx * typ * cnstr list ref * depend
     (* D ; Psi |- M <= A provided constraint *)
    | MPInst   of name * head option ref * mctx * dctx * typ * cnstr list ref * depend
    | MSInst   of name * sub option ref * mctx * dctx * dctx * cnstr list ref * depend
     (* cD ; cPsi |- s <= cPhi *)

  and tvar =
    | TInst   of typ option ref * dctx * kind * cnstr list ref

  and typ_free_var = Type of typ | TypVar of tvar

  and constrnt =                             (* Constraint                     *)
    | Queued                                 (* constraint ::= Queued          *)
    | Eqn of mctx * dctx * normal * normal   (*            | Psi |-(M1 == M2)  *)
    | Eqh of mctx * dctx * head * head       (*            | Psi |-(H1 == H2)  *)
    | Eqs of mctx * dctx * sub * sub         (*            | Psi |-(s1 == s2)  *)

  and cnstr = constrnt ref

  and dctx =                                 (* LF Context                     *)
    | Null                                   (* Psi ::= .                      *)
    | CtxVar   of ctx_var                    (* | psi                          *)
    | DDec     of dctx * typ_decl            (* | Psi, x:A   or x:block ...    *)

  and ctx_var =
    | CtxName   of name
    | CtxOffset of offset
    | CInst  of name * dctx option ref * cid_schema * mctx * msub
        (* D |- Psi : schema   *)

  and 'a ctx =                           (* Generic context declaration    *)
    | Empty                              (* Context                        *)
    | Dec of 'a ctx * 'a                 (* C ::= Empty                    *)
                                         (* | C, x:'a                      *)

  and sch_elem =                         (* Schema Element                 *)
    | SchElem of typ_decl ctx * typ_rec    (* Pi    x1:A1 ... xn:An.
                                            Sigma y1:B1 ... yk:Bk. B       *)
                                         (* Sigma-types not allowed in Ai  *)

  and schema =
    | Schema of sch_elem list

  and psi_hat = ctx_var option * offset  (* Psihat ::=         *)
                                         (*        | psi       *)
                                         (*        | .         *)
                                         (*        | Psihat, x *)


  and typ_rec =    (* Sigma x1:A1 ... xn:An. B *)
    |  SigmaLast of name option * typ                             (* ... . B *)
    |  SigmaElem of name * typ * typ_rec            (* xk : Ak, ... *)

  and tuple =
    | Last of normal
    | Cons of normal * tuple

  and mctx = ctyp_decl ctx          (* Modal Context  D: CDec ctx     *)


  (**********************)
  (* Type Abbreviations *)
  (**********************)
  
  type nclo     = normal  * sub          (* Ns = [s]N                      *)
  type sclo     = spine   * sub          (* Ss = [s]S                      *)
  type tclo     = typ     * sub          (* As = [s]A                      *)
  type trec_clo = typ_rec * sub          (* [s]Arec                        *)

  type assoc = Left | Right | NoAssoc
  type fix = Prefix | Postfix | Infix
  type prag =
    | NamePrag of cid_typ
    | NotPrag
    | OpenPrag of module_id
    | DefaultAssocPrag of assoc
    | FixPrag of name * fix * int * assoc option
    | AbbrevPrag of string list * string

  (* val blockLength : typ_rec -> int *)
  let rec blockLength = function
    | SigmaLast _ -> 1
    | SigmaElem(_x, _tA, recA) -> 1 + blockLength recA

  (* getType traverses the typ_rec from left to right;
     target is relative to the remaining suffix of the type

     getType head s_recA target j = (tA, s')

     if  Psi(head) = Sigma recA'
         and [s]recA is a suffix of recA'
     then
         Psi |- [s']tA  <= type

     CLIENTS: pass 1 for the last argument j

    (* getType head s_recA target 1 *)
    val getType : head -> trec_clo -> int -> int -> tclo
  *)
  let rec getType head s_recA target j = match (s_recA, target) with
    | ((SigmaLast (_, lastA), s), 1) ->
        (lastA, s)

    | ((SigmaElem (_x, tA, _recA), s), 1) ->
        (tA, s)

    | ((SigmaElem (_x, _tA, recA), s), target) ->
        let tPj = Proj (head, j) in
          getType head (recA, Dot (Head tPj, s)) (target - 1) (j + 1)

    | _ -> raise Not_found
 
  (* getIndex traverses the typ_rec from left to right;
     target is the name of the projection we're looking for

    Precondition: acc is 1 when the function is 1st called
     acc is an accumulator set to 1 when the function is called

  *)
let rec getIndex' trec target acc = match trec with
  | SigmaLast(None, _) -> raise Not_found
  | SigmaLast(Some name, _) ->
    if String.compare (name.string_of_name) (target.string_of_name) == 0 then acc
    else failwith "Projection Not found"
  | SigmaElem(name, _, trec') ->
    if String.compare (name.string_of_name) (target.string_of_name) == 0 then acc
  else getIndex' trec' target (acc + 1)

let getIndex head s_recA target acc = 
  let (trec, _) = s_recA in getIndex' trec target acc
  (* match s_recA with
    | (SigmaLast(None, _), _) -> raise Not_found
    | (SigmaLast(Some name, _),_) ->
      if String.compare (name.string_of_name) (target.string_of_name) == 0 then acc
      else raise Not_found

    | (SigmaElem (name, _tA, recA), s) -> 
      if String.compare (name.string_of_name) (target.string_of_name) == 0 then acc
      else let tPj = Proj (head, acc) in
      getIndex head (recA, Dot (Head tPj, s)) (target) (acc + 1) *)

end



(** Internal Computation Syntax *)
module Comp = struct
  type  kind =
    | Ctype of Loc.t
    | PiKind  of Loc.t * LF.ctyp_decl * kind

  type meta_typ =
    | MetaTyp of LF.typ * LF.dctx
    | MetaParamTyp of LF.typ * LF.dctx
    | MetaSubTyp of LF.dctx * LF.dctx
    | MetaSchema of cid_schema

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
  (* MetaSClo of meta_spine * msub *)

  type typ =
    | TypBase   of Loc.t * cid_comp_typ * meta_spine
    | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
    | TypDef    of Loc.t * cid_comp_typ * meta_spine
    | TypBox of Loc.t * meta_typ 
(*  | TypBox    of Loc.t * LF.typ  * LF.dctx *)
    | TypParam  of Loc.t * LF.typ  * LF.dctx
    | TypSub    of Loc.t * LF.dctx * LF.dctx
    | TypArr    of typ * typ
    | TypCross  of typ * typ
    | TypPiBox  of LF.ctyp_decl * typ
    | TypClo    of typ *  LF.msub
    | TypBool

  type ctyp_decl =
    | CTypDecl    of name * typ
    | CTypDeclOpt of name

  type gctx = ctyp_decl LF.ctx

  type env =
    | Empty
    | Cons of value * env

  and value =
    | FunValue   of name * exp_chk * LF.msub * env
    | RecValue   of cid_prog * exp_chk * LF.msub * env
    | MLamValue  of name * exp_chk * LF.msub * env
    | CtxValue   of name * exp_chk * LF.msub * env
    | BoxValue   of meta_obj
    | ParamValue of LF.psi_hat * LF.head
    | PsiValue   of LF.dctx
    | ConstValue of cid_prog
    | DataValue  of cid_comp_const * data_spine
    | BoolValue  of bool
    | PairValue  of value * value
    | CofunValue of (copattern_spine * exp_chk) list * LF.msub * env
    | CodataValue of cid_comp_dest * codata_spine

  and exp_chk =
    | Syn    of Loc.t * exp_syn
    | Rec    of Loc.t * name * exp_chk
    | Fun    of Loc.t * name * exp_chk
    | Cofun  of Loc.t * (copattern_spine * exp_chk) list
    | MLam   of Loc.t * name * exp_chk
    | Pair   of Loc.t * exp_chk * exp_chk
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk)
    | Let    of Loc.t * exp_syn * (name * exp_chk)
    | Box    of Loc.t * meta_obj
    | Case   of Loc.t * case_pragma * exp_syn * branch list
    | If     of Loc.t * exp_syn * exp_chk * exp_chk
    | Hole   of Loc.t * (unit -> int)

  and exp_syn =
    | Var    of Loc.t * offset
    | DataConst of Loc.t * cid_comp_const
    | DataDest of Loc.t * cid_comp_dest
    | Const  of Loc.t * cid_prog
    | Apply  of Loc.t * exp_syn * exp_chk
    | MApp   of Loc.t * exp_syn * meta_obj
    | Ann    of exp_chk * typ
    | Equal  of Loc.t * exp_syn * exp_syn
    | PairVal of Loc.t * exp_syn * exp_syn
    | Boolean of bool

  and branch_pattern =
    | NormalPattern of LF.normal * exp_chk
    | EmptyPattern

  and pattern =
    | PatEmpty   of Loc.t * LF.dctx
    | PatMetaObj of Loc.t * meta_obj
    | PatConst of Loc.t * cid_comp_const * pattern_spine
    | PatFVar   of Loc.t * name
    | PatVar   of Loc.t * offset
    | PatPair  of Loc.t * pattern * pattern
    | PatTrue  of Loc.t
    | PatFalse of Loc.t
    | PatAnn   of Loc.t * pattern * typ

  and pattern_spine =
    | PatNil
    | PatApp of Loc.t * pattern * pattern_spine

  (* Arguments in data spines are accumulated in reverse order, to
     allow applications of data values in constant time. *)
  and data_spine =
    | DataNil
    | DataApp of value * data_spine

  and codata_spine =
    | CodataNil
    | CodataApp of value * codata_spine

  and branch =
    | EmptyBranch of Loc.t * LF.ctyp_decl LF.ctx * pattern * LF.msub
    | Branch of Loc.t * LF.ctyp_decl LF.ctx  * gctx * pattern * LF.msub * exp_chk

    | BranchBox of LF.mctx * LF.mctx * (LF.dctx * branch_pattern * LF.msub * LF.csub)

    | BranchSBox of Loc.t * LF.ctyp_decl LF.ctx * LF.ctyp_decl LF.ctx *
        (LF.dctx * LF.sub * LF.msub * LF.csub) * exp_chk

  and copattern_spine =
    | CopatNil of Loc.t
    | CopatApp of Loc.t * cid_comp_dest * copattern_spine
    | CopatMeta of Loc.t * meta_obj * copattern_spine

  type tclo = typ * LF.msub

end


(** Internal Signature Syntax *)
module Sgn = struct

  type decl =
    | Typ           of Loc.t * cid_typ  * LF.kind
    | Const         of Loc.t * cid_term * LF.typ
    | CompTyp       of Loc.t * name * Comp.kind
    | CompCotyp     of Loc.t * name * Comp.kind
    | CompConst     of Loc.t * name * Comp.typ
    | CompDest      of Loc.t * name * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema        of cid_schema * LF.schema
    | Rec           of (cid_prog   * Comp.typ * Comp.exp_chk) list
    | Pragma        of LF.prag
    | Val           of Loc.t * name * Comp.typ * Comp.exp_chk * Comp.value option
    | MRecTyp       of Loc.t * decl list list
    | Module        of Loc.t * string * decl list
    | Query         of Loc.t * name option * (LF.typ  * Id.offset) * int option * int option
    | Comment       of Loc.t * string

  type sgn = decl list

end
