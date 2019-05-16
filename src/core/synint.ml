(* Internal Syntax *)
(* Internal LF Syntax *)
open Id
open Pragma


module Loc = Camlp4.PreCast.Loc

module LF = struct

  type depend =
    | No      (* Explicit *)
    | Maybe   (* Implicit *)
    | Inductive

  type kind =
    | Typ
    | PiKind of (typ_decl * depend) * kind

  and typ_decl =                              (* LF Declarations                *)
    | TypDecl of name * typ                   (* D := x:A                       *)
    | TypDeclOpt of name                      (*   |  x:_                       *)

  and cltyp =
    | MTyp of typ
    | PTyp of typ
    | STyp of svar_class * dctx

  and svar_class =
    | Ren
    | Subst

  and ctyp =
    | ClTyp of cltyp * dctx
    | CTyp of cid_schema option

  and ctyp_decl =                             (* Contextual Declarations        *)
    | Decl of name * ctyp * depend
    | DeclOpt of name

  and typ =                                   (* LF level                       *)
    | Atom  of Loc.t * cid_typ * spine        (* A ::= a M1 ... Mn              *)
    | PiTyp of (typ_decl * depend) * typ      (*   | Pi x:A.B                   *)
    | Sigma of typ_rec
    | TClo  of (typ * sub)                    (*   | TClo(A,s)                  *)


  and normal =                                (* normal terms                   *)
    | Lam  of Loc.t * name * normal           (* M ::= \x.M                     *)
    | Root of Loc.t * head * spine            (*   | h . S                      *)
    | LFHole of Loc.t * string option
    | Clo  of (normal * sub)                  (*   | Clo(N,s)                   *)
    | Tuple of Loc.t * tuple

  and head =
    | BVar  of offset                         (* H ::= x                        *)
    | Const of cid_term                       (*   | c                          *)
    | MMVar of mm_var_inst                    (*   | u[t ; s]                   *)
    | MPVar of mm_var_inst                    (*   | p[t ; s]                   *)
    | MVar  of (cvar * sub)                   (*   | u[s]                       *)
    | PVar  of (offset * sub)                 (*   | p[s]                       *)
    | AnnH  of head * typ                     (*   | (H:A)                      *)
    | Proj  of head * int                     (*   | x.k | #p.k s               *)

    | FVar  of name                           (* free variable for type
                                                 reconstruction                 *)
    | FMVar of fvarsub                        (* free meta-variable for type
                                                 reconstruction                 *)
    | FPVar of fvarsub                        (* free parameter variable for type
                                                 reconstruction                 *)
    | HClo  of offset * offset * sub          (*   | HClo(x, #S[sigma])         *)
    | HMClo of offset * mm_var_inst           (*   | HMClo(x, #S[theta;sigma])  *)

  and fvarsub = name * sub
  and spine =                                 (* spine                          *)
    | Nil                                     (* S ::= Nil                      *)
    | App  of normal * spine                  (*   | M . S                      *)
    | SClo of (spine * sub)                   (*   | SClo(S,s)                  *)

  and sub =
    | Shift of offset                         (* sigma ::= ^(psi,n)             *)
    | SVar  of offset * int * sub (* BEWARE: offset and int are both ints,
                                     and in the opposite order compared to FSVar and MSVar.
				     offset is the index into Delta and describes the SVar.
                                     This is a pain to fix *)
    | FSVar of offset * fvarsub               (*   | s[sigma]                   *)
    | Dot   of front * sub                    (*   | Ft . s                     *)
    | MSVar of offset * mm_var_inst           (*   | u[t ; s]                   *)
    | EmptySub
    | Undefs

  and front =                                 (* Fronts:                        *)
    | Head of head                            (* Ft ::= H                       *)
    | Obj  of normal                          (*    | N                         *)
    | Undef                                   (*    | _                         *)

                                              (* Contextual substitutions       *)
  and mfront =                                (* Fronts:                        *)
    | ClObj of psi_hat * clobj
    | CObj of dctx                            (*    | Psi                       *)
    | MV   of offset                          (*    | u//u | p//p | psi/psi     *)
    | MUndef (* This shouldn't be here, we should use a different datastructure for
               partial inverse substitutions *)

  and clobj =                                 (* ContextuaL objects *)
    | MObj of normal                          (* Mft::= Psihat.N                *)
    | PObj of head                            (*    | Psihat.p[s] | Psihat.x    *)
    | SObj of sub

  and msub =                                  (* Contextual substitutions       *)
    | MShift of int                           (* theta ::= ^n                   *)
    | MDot   of mfront * msub                 (*       | MFt . theta            *)

  and cvar =                                  (* Contextual Variables           *)
    | Offset of offset                        (* Bound Variables                *)
    | Inst   of mm_var                 (* D ; Psi |- M <= A provided constraint *)

  and mm_var = name * iterm option ref * mctx * ctyp * cnstr list ref * depend
  and mm_var_inst' = mm_var * msub
  and mm_var_inst = mm_var_inst' * sub

  and iterm =
    | INorm of normal
    | IHead of head
    | ISub of sub
    | ICtx of dctx

  and tvar =
    | TInst   of typ option ref * dctx * kind * cnstr list ref

  and typ_free_var = Type of typ | TypVar of tvar

  and constrnt =                             (* Constraint                     *)
    | Queued                                 (* constraint ::= Queued          *)
    | Eqn of mctx * dctx * iterm * iterm     (*            | Delta; Psi |-(M1 == M2)  *)

  and cnstr = constrnt ref

  and dctx =                                 (* LF Context                     *)
    | Null                                   (* Psi ::= .                      *)
    | CtxVar   of ctx_var                    (* | psi                          *)
    | DDec     of dctx * typ_decl            (* | Psi, x:A   or x:block ...    *)

  and ctx_var =
    | CtxName   of name
    | CtxOffset of offset
    | CInst  of mm_var_inst'
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
    |  SigmaLast of name option * typ                        (* ... . B *)
    |  SigmaElem of name * typ * typ_rec                (* xk : Ak, ... *)

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
  let rec getIndex' trec target acc =
    match trec with
    | SigmaLast(None, _) -> raise Not_found
    | SigmaLast(Some name, _) ->
       if String.compare (string_of_name name) (string_of_name target) == 0
       then acc
       else failwith "Projection Not found"
    | SigmaElem(name, _, trec') ->
       if String.compare (string_of_name name) (string_of_name target) == 0
       then acc
       else getIndex' trec' target (acc + 1)

  let getIndex trec target = getIndex' trec target 1

  let is_explicit =
    function
    | Decl(_, _, dep) ->
       begin
         match dep with
         | No -> true
         | Maybe -> false
         | Inductive -> true
       end
    | _ -> true

  let name_of_ctyp_decl (d : ctyp_decl) =
    match d with
    | Decl (n, _, _) -> n
    | DeclOpt n -> n
end

(* Internal Computation Syntax *)
module Comp = struct

  type  kind =
    | Ctype of Loc.t
    | PiKind  of Loc.t * LF.ctyp_decl * kind

  type meta_typ = LF.ctyp

  type meta_obj = Loc.t * LF.mfront

  type meta_spine =
    | MetaNil
    | MetaApp of meta_obj * meta_spine

  type typ =
    | TypBase   of Loc.t * cid_comp_typ * meta_spine
    | TypCobase of Loc.t * cid_comp_cotyp * meta_spine
    | TypDef    of Loc.t * cid_comp_typ * meta_spine
    | TypBox of Loc.t * meta_typ
    | TypArr    of typ * typ
    | TypCross  of typ * typ
    | TypPiBox  of LF.ctyp_decl * typ
    | TypClo    of typ *  LF.msub
    | TypInd of typ


  (* For ih *)
  type args =
    | M  of meta_obj
    | V  of offset
    | E
    | DC (* don't care *)

  type wf_tag = bool  (* indicates whether the argument is smaller *)

  type ctyp_decl =
    | WfRec of name * args list * typ
    | CTypDecl    of name * typ * wf_tag
    | CTypDeclOpt of name

  type gctx = ctyp_decl LF.ctx

  type env =
    | Empty
    | Cons of value * env

  and value =
    | FnValue    of name * exp_chk * LF.msub * env
    | FunValue   of fun_branches_value
    | RecValue   of cid_prog * exp_chk * LF.msub * env
    | MLamValue  of name * exp_chk * LF.msub * env
    | CtxValue   of name * exp_chk * LF.msub * env
    | BoxValue   of meta_obj
    | ConstValue of cid_prog
    | DataValue  of cid_comp_const * data_spine
    | PairValue  of value * value

  and exp_chk =
    | Syn    of Loc.t * exp_syn
    | Rec    of Loc.t * name * exp_chk
    | Fn     of Loc.t * name * exp_chk
    | Fun    of Loc.t * fun_branches
    | MLam   of Loc.t * name * exp_chk
    | Pair   of Loc.t * exp_chk * exp_chk
    | LetPair of Loc.t * exp_syn * (name * name * exp_chk)
    | Let    of Loc.t * exp_syn * (name * exp_chk)
    | Box    of Loc.t * meta_obj
    | Case   of Loc.t * case_pragma * exp_syn * branch list
    | Hole   of Loc.t * string option

  and exp_syn =
    | Var    of Loc.t * offset
    | DataConst of Loc.t * cid_comp_const
    | Obs    of Loc.t * exp_chk * LF.msub * cid_comp_dest
    | Const  of Loc.t * cid_prog
    | Apply  of Loc.t * exp_syn * exp_chk
    | MApp   of Loc.t * exp_syn * meta_obj
    | Ann    of exp_chk * typ
    | PairVal of Loc.t * exp_syn * exp_syn

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
    | PatAnn   of Loc.t * pattern * typ

  and pattern_spine =
    | PatNil
    | PatApp of Loc.t * pattern * pattern_spine
    | PatObs of Loc.t * cid_comp_dest * LF.msub * pattern_spine

  (* Arguments in data spines are accumulated in reverse order, to
     allow applications of data values in constant time. *)
  and data_spine =
    | DataNil
    | DataApp of value * data_spine

  and branch =
    | EmptyBranch of Loc.t * LF.ctyp_decl LF.ctx * pattern * LF.msub
    | Branch of
        Loc.t
        * LF.mctx
        * gctx
        * pattern
        * LF.msub (* refinement substitution for the branch *)
        * exp_chk

  and fun_branches =
   | NilFBranch of Loc.t
   | ConsFBranch of Loc.t * (LF.mctx * gctx * pattern_spine * exp_chk) * fun_branches

  and fun_branches_value =
  | NilValBranch
  | ConsValBranch of (pattern_spine * exp_chk * LF.msub * env) * fun_branches_value


  type tclo = typ * LF.msub

  let itermToClObj = function
    | LF.INorm n -> LF.MObj n
    | LF.IHead h -> LF.PObj h
    | LF.ISub s -> LF.SObj s
  let metaObjToMFront (loc,x) = x

  (* Bundle of LF and computational hypotheses. *)
  type hypotheses =
    { cD : LF.mctx (* Delta / meta context / LF assumptions *)
    ; cG : gctx    (* Gamma / computation assumptions *)
    }

  let no_hypotheses = { cD = LF.Empty; cG = LF.Empty }

  (* A proof is a sequence of statements ending either as a complete proof or an incomplete proof.
   * The type parameter 'a is used as a trick to rule out incomplete proofs:
   * - if 'a = void then the Incomplete constructor is impossible
   * - if 'a = unit then this is a true incomplete proof.
   *)
  type 'a proof =
    | QED (* proof complete *)
    | Incomplete (* hole *)
      of 'a * 'a proof_state
    | ProofCons of 'a statement * 'a proof (* another step in the proof *)

  and 'a proof_state =
    { context : hypotheses
    ; goal : tclo
    ; mutable solution : 'a proof option
    }

  and 'a statement =
    | Directive of 'a directive
    | Claim
      of name option (* Stated claims may optionally be named by a variable. *)
         * LF.mctx (* the context in which to interpret the meta-variables occurring in the type *)
         * exp_chk option
         (* ^ the term that justifies the claim; filled in by proof
          * search if the user doesn't specify it *)
         * tclo

  and 'a directive =
    | Intros (* Prove a function type by a hypothetical derivation. *)
      of 'a hypothetical
    | InductionHypothesis (* Invocation of the IH *)
      of exp_chk list (* the terms to invoke the IH with *)
         * name (* name the result of the IH *)
    | Split (* Splitting on an LF object *)
      of exp_syn (* The object to split on *)
         * typ (* The type of the object that we're splitting on *)
         * 'a split_branch list

  (** A branch of a case analysis. *)
  and 'a split_branch =
    | SplitBranch
      of (* LF.msub (* refinement substitution for the branch *) * *)
           'a hypothetical (* the derivation for this case *)

 (** A hypothetical derivation lists meta-hypotheses and
     hypotheses, then proceeds with a proof.
  *)
  and 'a hypothetical =
    Hypothetical of hypotheses * 'a proof

  let make_proof_state (t : tclo) : 'a proof_state =
    { context = no_hypotheses
    ; goal = t
    ; solution = None
    }

  type complete_proof = Misc.void proof
  type incomplete_proof = unit proof

  (** Smart constructor for an unfinished proof ending. *)
  let incomplete_proof (s : unit proof_state) : incomplete_proof =
    Incomplete ( (), s )

  (** Smart constructor for the intros directive. *)
  let intros (ctx : hypotheses) (proof : 'a proof) : 'a statement =
    Directive (Intros (Hypothetical (ctx, proof)))

  let proof_cons (stmt : 'a statement) (proof : 'a proof) = ProofCons (stmt, proof)

  let claim ?name:(name = None) ?term:(term = None) (cD : LF.mctx) (t : tclo) =
    Claim (name, cD, term, t)

  let split (m : exp_syn) (tau : typ) (bs : 'a split_branch list) : 'a statement =
    Directive (Split (m, tau, bs))

  let split_branch (h : hypotheses) (d : 'a proof) : 'a split_branch =
    SplitBranch (Hypothetical (h, d))

  let name_of_ctyp_decl (d : ctyp_decl) =
    match d with
    | CTypDecl (name, _, _) -> name
    | CTypDeclOpt name -> name
    | WfRec (name, _, _) -> name
end


(* Internal Signature Syntax *)
module Sgn = struct

  (* type positivity_flag =  *)
  (*   | Noflag *)
  (*   | Positivity *)
  (*   | Stratify of Loc.t * Comp.order * name * (name option) list  *)


  type positivity_flag =
    | Nocheck
    | Positivity
    | Stratify of  Loc.t * int
    | StratifyAll of Loc.t



  type decl =
    | Typ           of Loc.t * cid_typ  * LF.kind
    | Const         of Loc.t * cid_term * LF.typ
    | CompTyp       of Loc.t * name * Comp.kind  *  positivity_flag
    | CompCotyp     of Loc.t * name * Comp.kind
    | CompConst     of Loc.t * name * Comp.typ
    | CompDest      of Loc.t * name * LF.mctx * Comp.typ * Comp.typ
    | CompTypAbbrev of Loc.t * name * Comp.kind * Comp.typ
    | Schema        of cid_schema * LF.schema
    | Rec           of (cid_prog   * Comp.typ * Comp.exp_chk) list
    | Proof         of Comp.typ * Comp.incomplete_proof
    | Pragma        of LF.prag
    | Val           of Loc.t * name * Comp.typ * Comp.exp_chk * Comp.value option
    | MRecTyp       of Loc.t * decl list list
    | Module        of Loc.t * string * decl list
    | Query         of Loc.t * name option * (LF.typ  * Id.offset) * int option * int option
    | Comment       of Loc.t * string

  type sgn = decl list

end
