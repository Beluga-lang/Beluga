(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
*)
open Store
open Store.Cid
open Substitution
open Syntax
open Id

module S    = Substitution.LF
module I    = Int.LF
module Comp = Int.Comp

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [6])

exception NotImplemented

exception Error of string

let leftoverMeta2 =
    "Leftover uninstantiated meta²-variable during reconstruction;\n"
  ^ "the user needs to supply more information, since the type of\n"
  ^ "a given expression is not uniquely determined."

(* ******************************************************************* *)
(* Abstraction:

   - Abstract over the meta-variables in O
   - Abstract over the free variables in F

   Abstraction only succeeds, if O and F are not cyclic.

  We write {{Q}} for the context of Q, where MVars and FVars have
  been translated to declarations and their occurrences to BVars.
  We write {{A}}_Q, {{M}}_Q, {{S}}_Q for the corresponding translation
  of a type, an expression or spine.

  Just like contexts Psi, any Q is implicitly assumed to be
  well-formed and in dependency order. ** note that Q may contain
  cyclic dependencies, which need to be detected **

  We write  Q ; Psi ||- M  if all MVars and FVars in M and Psi are
  collected in Q. In particular, . ; Psi ||- M means M and Psi contain
  no MVars or FVars.  Similarly, for spines . ; Psi ||- S and other
  syntactic categories.

  Abstraction proceeds in three phases:

   - Collection of all MVars and FVars in M into Q;

   - Abstraction over all MVars and FVars (which are listed in Q)
     and occur in M, will yield a new term M'

   -

 Collection and abstraction raise Error if there are unresolved
  constraints after simplification.



   Collection will work in a generic way so we can collect 
   - FVar  (named free LF-bound variables),  
   - FMVar (named free meta-variables),  
   - FPVar (named free parameter variables),  

   - MVars (references to meta-variables representing unknowns)

   Abstraction over LF-bound variables and abstraction of named
   meta-variables and parameter variables are however kept separate. 

   Abstraction over LF-bound variables is performed by the functions
   abstractTerm, abstractType, etc.

   Abstraction over meta-variables and parameter variables is
   performed by the functions abstractMVarTerm, abstractMVarType, etc.


   


*)


type free_var =
  (* Free variables (references): unnamed *)

  (* For MMV, MV and PV it suffices to store the reference for the
     respective MMVar, MVar and PVar; the substitution associated with an
     MMVar, MVar and PVar is irrelevant here *)

  | MMV of I.head         (* Y ::= u[ms,s]   where h = MMVar(u, cD, Psi, P, _)  
                             and    cD' ; Psi' |- u[ms, s] <= [ms ; s]P      *)
  | MV of I.head          (* Y ::= u[s]   where h = MVar(u, Psi, P, _)  
                             and    cD' ; Psi' |- u[s] <= [s]P               *)
  | PV of I.head          (*    |  p[s]   where h = PVar(p, Psi, A, _)
                             and    cD' ; Psi' |- p[s] <= [s]A               *)

  (* Free named variables *)
  | FV of Id.name * I.typ option 
                                (*     | (F, A)                  . |- F <= A *)

  | FMV of Id.name * (I.typ * I.dctx) option 
                     (*     | (F, (A, cPsi))                  cPsi |- F <= A *)

  | FPV of Id.name * (I.typ * I.dctx) option 
                     (*     | (F, (A, cPsi))                  cPsi |- F <= A *)


let rec raiseType cPsi tA = match cPsi with
  | I.Null -> (None, tA)
  | I.CtxVar psi -> (Some psi, tA)
  | I.DDec (cPsi', decl) ->
      raiseType cPsi' (I.PiTyp ((decl, I.Maybe), tA))

let rec raiseKind cPsi tK = match cPsi with
  | I.Null -> tK
  | I.DDec (cPsi', decl) ->
      raiseKind cPsi' (I.PiKind ((decl, I.Maybe), tK))

let ctxVarToString psi = match psi with
  | None -> " "
  | Some (I.CtxOffset k) -> "Ctx_Var " ^ string_of_int k

let rec collectionToString cQ = match cQ with
  | I.Empty -> ""

  | I.Dec(cQ, MV ((I.MVar (I.Inst(_r, cPsi, tP, _c), _s)) as h)) -> 
      let (ctx_var, tA) = raiseType cPsi tP in        
      let cO = I.Empty in 
      let cD = I.Empty in 
        collectionToString cQ ^ " "
      ^ P.normalToString cO cD I.Null  (I.Root(None, h, I.Nil), LF.id)
      ^ " : "
      ^ ctxVarToString ctx_var
      ^ " . "
      ^ P.typToString cO cD I.Null (tA , LF.id)
      ^ "\n"

  | I.Dec(cQ, MMV ((I.MMVar (I.MInst(_r, cD, cPsi, tP, _c), _s)) as h)) -> 
      let (ctx_var, tA) = raiseType cPsi tP in        
      let cO = I.Empty in 
       collectionToString cQ ^ " "
     ^ P.normalToString cO cD I.Null  (I.Root(None, h, I.Nil), LF.id)
     ^ " : "
     ^ ctxVarToString ctx_var
     ^ " . "
     ^ P.typToString cO cD I.Null (tA , LF.id)
     ^ "\n"

  | I.Dec (cQ, FMV (u, Some (tP, cPhi))) -> 
      let cO = I.Empty in 
      let cD = I.Empty in 
       collectionToString cQ 
     ^ " " ^ R.render_name u ^ " : "
     ^ P.typToString cO cD cPhi (tP, LF.id)
     ^ " [ "  ^ P.dctxToString cO cD cPhi ^ "]\n" 
                          
  | I.Dec(cQ, PV ((I.PVar (I.PInst(_r, cPsi, tA', _c), _s)) as h)) -> 
      let (ctx_var, tA) = raiseType cPsi tA' in        
      let cO = I.Empty in 
      let cD = I.Empty in 
       collectionToString cQ 
     ^ " " ^ P.normalToString cO cD I.Null (I.Root(None, h, I.Nil), LF.id) ^ " : "
     ^ P.typToString cO cD I.Null (tA', LF.id)
     ^ " : "
     ^ ctxVarToString ctx_var ^ " . " ^ P.typToString cO cD I.Null (tA , LF.id)
     ^ "\n"

  | I.Dec(cQ, FV (_n, None)) ->  collectionToString cQ ^ ",  FV _ .\n"

  | I.Dec(cQ, FV (n, Some tA)) -> 
      let cO = I.Empty in 
      let cD = I.Empty in       
        collectionToString cQ ^ ",  FV " ^ n.string_of_name ^ " : "
      ^ "(" ^ P.typToString cO cD I.Null (tA, LF.id) ^ ")"
      ^ "\n"

  | I.Dec(cQ, FPV (n, Some (tA, cPsi))) -> 
      let (ctx_var, tA') = raiseType cPsi tA in        
      let cO = I.Empty in 
      let cD = I.Empty in       
        collectionToString cQ
      ^ " FPV " ^ n.string_of_name ^ " : "
      ^ ctxVarToString ctx_var ^ "." ^ P.typToString cO cD I.Null (tA', LF.id)
      ^ "\n"

let printCollection s = print_string (collectionToString s)



(* exists p cQ = B
   where B iff cQ = cQ1, Y, cQ2  s.t. p(Y)  holds
*)
let rec exists p = function
  | I.Empty        -> false
  | I.Dec(cQ', y)  -> p y || exists p cQ'

(* length cPsi = |cPsi| *)
let length cPsi = 
  let (_, n) = Context.dctxToHat cPsi in
    n


(* Eta-expansion of bound variables which have function type *)
let rec etaExpandHead loc h tA = 
  let rec etaExpSpine k tS tA = begin match  tA with
    | I.Atom _  -> (k, tS)
        
    | I.PiTyp (_ , tA') -> 
        let tN = I.Root(loc, I.BVar k, I.Nil) in                   
          etaExpSpine (k+1)  (I.App(tN, tS)) tA'
  end in 
    
  let rec etaExpPrefix loc (tM, tA) = begin match tA with
    | I.Atom _ -> tM
    | I.PiTyp ((I.TypDecl (x, _ ), _ ) , tA') -> 
        I.Lam (loc, x, etaExpPrefix loc (tM, tA')) 
  end in
    
  let (k, tS') = etaExpSpine 1 (I.Nil) tA in 
  let h'       =  begin match h with 
                    | I.BVar x -> I.BVar (x+k-1)
                    | I.FVar _ -> h 
                  end  in
    etaExpPrefix loc (I.Root(loc, h' , tS'), tA)   




(* eqMMVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let rec eqMMVar mmV1 mmV2 = match (mmV1, mmV2) with
  | (I.MMVar (I.MInst (r1, _, _, _, _), _s) , MMV (I.MMVar (I.MInst (r2, _, _, _, _), _s'))) -> 
       r1 == r2
  | _ -> false


(* eqMVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let rec eqMVar mV1 mV2 = match (mV1, mV2) with
  | (I.MVar (I.Inst (r1, _, _, _), _s) , MV (I.MVar (I.Inst (r2, _, _, _), _s'))) -> 
       r1 == r2
  | _ -> false



(* eqPVar mV mV' = B
   where B iff mV and mV' represent same variable
*)
let rec eqPVar mV1 mV2 = match (mV1, mV2) with
  | (I.PVar (I.PInst (r1, _, _, _), _s) , PV (I.PVar (I.PInst (r2, _, _, _), _s'))) -> 
       r1 == r2
  | _ -> false

(* eqFVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FV (n2, _)) -> (n1 = n2)
  | _ -> false


(* eqFMVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFMVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FMV (n2, _)) -> (n1 = n2)
  | _ -> false


(* eqFPVar n fV' = B
   where B iff n and fV' represent same variable
*)
let rec eqFPVar n1 fV2 = match (n1, fV2) with
  | (n1 ,  FPV (n2, _)) -> (n1 = n2)
  | _ -> false


let rec phatToDCtx phat = match phat with 
  | (None,      0) -> I.Null
  | (Some psi , 0) -> I.CtxVar psi
  | (ctx_v    , k) -> 
      I.DDec (phatToDCtx (ctx_v, k-1), I.TypDeclOpt (Id.mk_name Id.NoName)) 

let rec constraints_solved cnstr = match cnstr with
  | [] -> true
  | ({contents = I.Queued} :: cnstrs) -> 
      constraints_solved cnstrs 
  | ({contents = I.Eqn (_cD, phat, tM, tN)} :: cnstrs) -> 
      if Whnf.conv (tM, LF.id) (tN, LF.id) then 
        constraints_solved cnstrs
      else 
        (Printf.printf "Encountered unsolved constraint:\n %s  =   %s\n\n"
           (P.normalToString I.Empty I.Empty (phatToDCtx phat) (tM, LF.id))
           (P.normalToString I.Empty I.Empty (phatToDCtx phat) (tN, LF.id));         
         false )
 | ({contents = I.Eqh (_cD, _phat, h1, h2)} :: cnstrs) -> 
      if Whnf.convHead (h1, LF.id) (h2, LF.id) then 
        constraints_solved cnstrs
      else false 



(* Check that a synthesized computation-level type is free of constraints *)
let rec cnstr_ctyp tau =  match tau  with
  | Comp.TypBox (_, tA, cPsi) -> cnstr_typ (tA, LF.id) && cnstr_dctx cPsi

and cnstr_typ sA = match sA with
  | (I.Atom  (_, _a, spine),  s)  -> cnstr_spine (spine , s)

  | (I.PiTyp ((t_decl, _ ), tB),  s) -> 
      cnstr_typ_decl (t_decl, s) && cnstr_typ (tB, LF.dot1 s)

  | (I.Sigma t_rec,  s) -> cnstr_typ_rec (t_rec, s)

and cnstr_term sM = match sM with
  | (I.Lam(_ , _x , tM), s) -> cnstr_term (tM, LF.dot1 s) 
  | (I.Root (_, h, spine), s) -> 
      cnstr_head h && cnstr_spine (spine, s)

and cnstr_spine sS = match sS with
  | (I.Nil, _s) -> false
  | (I.App(tM, tS), s) -> 
      cnstr_term (tM, s) && cnstr_spine (tS, s)
  | (I.SClo (tS, s'), s) -> cnstr_spine (tS, LF.comp s' s)


and cnstr_head h = match h with
  | I.MMVar(I.MInst (_r, _, _ , _ , cnstr), (_ms, s)) -> 
       (if constraints_solved (!cnstr) then 
          cnstr_sub s 
        else false)

  | I.MVar(I.Inst (_r, _ , _ , cnstr), s) -> 
       (if constraints_solved (!cnstr) then 
          cnstr_sub s 
        else false)

  | I.PVar(I.PInst (_p, _, _, {contents = cnstr}), s) -> 
      (if constraints_solved cnstr then 
         cnstr_sub s 
       else false)
        
 | I.Proj (I.PVar (I.PInst (_p, _, _, {contents = cnstr}), s), _ ) -> 
      (if constraints_solved cnstr then 
         cnstr_sub s 
       else false)
      
 |  _  -> false


and cnstr_sub s = match s with
  | I.Shift _ -> false
  | I.Dot (I.Head h , s) -> cnstr_head h && cnstr_sub s
  | I.Dot (I.Obj tM , s) -> cnstr_term (tM, LF.id) && cnstr_sub s
  | I.Dot (I.Undef, s')  -> cnstr_sub s'


and cnstr_dctx cPsi = match cPsi with
  | I.Null -> false
  | I.CtxVar _ -> false
  | I.DDec (cPsi, t_decl) -> cnstr_dctx cPsi && cnstr_typ_decl (t_decl, LF.id)


and cnstr_typ_decl st_decl = match st_decl with
  | (I.TypDecl (_ , tA), s) -> cnstr_typ (tA, s)
  | _ -> false


and cnstr_typ_rec (t_rec, s) = match t_rec with
  | I.SigmaLast tA -> cnstr_typ (tA, s)
  | I.SigmaElem (_, tA, t_rec) -> cnstr_typ (tA, s) && cnstr_typ_rec (t_rec, s)




(* index_of cQ n = i
   where cQ = cQ1, Y, cQ2 s.t. n = Y and length cQ2 = i
*)
let rec index_of cQ n = 
  match (cQ, n) with
  | (I.Empty, _) ->
      raise (Error "index_of for a free variable (FV, FMV, FPV, MV,  does not exist – should be impossible\n")  (* impossible due to invariant on collect *)

  | (I.Dec (cQ', MMV u1), MMV u2) ->
      (* TODO investigate the feasibility of having it start at 0 *)
      if eqMMVar u1 (MMV u2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', MV u1), MV u2) ->
      (* TODO investigate the feasibility of having it start at 0 *)
      if eqMVar u1 (MV u2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', PV p1), PV p2) ->
      (* TODO investigate the feasibility of having it start at 0 *)
      if eqPVar p1 (PV p2) then 1 else (index_of cQ' n) + 1 

  | (I.Dec (cQ', FV (f1, _)), FV (f2, tA)) ->
      if eqFVar f1 (FV (f2, tA)) then 1 else (index_of cQ' n) + 1

  | (I.Dec (cQ', FMV (u1, _)), FMV (u2, tA_cPsi)) ->
      if eqFMVar u1 (FMV (u2, tA_cPsi)) then 1 else (index_of cQ' n) + 1

  | (I.Dec (cQ', FPV (p1, _)), FPV (p2, tA_cPsi)) ->
      if eqFPVar p1 (FPV (p2, tA_cPsi)) then 1 else (index_of cQ' n) + 1


  | (I.Dec (cQ', _), _) ->
      (index_of cQ' n) + 1

(* If   cQ = cQ1 (MV u) cQ2
   and  u :: A[Psi]
   then (ctxToDctx cQ) = (ctxToDctx cQ1) Pi Psi . A (ctxToDctx cQ2)

   If   cQ = cQ1 (FV (F, A)) cQ2
   then (ctxToDctx cQ) = (ctxToDctx cQ1) A (ctxToDctx cQ2)
*)
let rec ctxToDctx cQ = match cQ with
  | I.Empty ->
      I.Null

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) ->
      begin match raiseType cPsi tA with
        | (None, tA') -> 
            let x = Id.mk_name (Id.MVarName (Typ.gen_var_name tA')) in 
            I.DDec (ctxToDctx cQ', I.TypDecl (x, tA'))
        | (Some _, _ ) -> raise (Error "ctxToDctx generates LF-dctx with context variable: should be impossible!")
      end 
  | I.Dec (cQ', FV (x, Some tA)) ->
      (* let x = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in  *)
      I.DDec (ctxToDctx cQ', I.TypDecl (x, tA))


let rec ctxToCtx cQ = match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) ->
      begin match raiseType cPsi tA with
        | (None, tA') -> 
            let x = Id.mk_name (Id.MVarName (Typ.gen_var_name tA')) in 
            I.Dec (ctxToCtx cQ', I.TypDecl (x, tA'))
        | (Some _, _ ) -> raise (Error "ctxToCtx generates LF-ctx with context variable: should be impossible!")
      end 
  | I.Dec (cQ', FV (x, Some tA)) ->
      (* let x = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in  *)
      I.Dec (ctxToCtx cQ', I.TypDecl (x, tA))



let rec ctxToMCtx cQ  = match cQ with
  | I.Empty ->
      I.Empty

  (* The case where cD is not empty, and an meta²-variable is uninstantiated
     should never happen. -bp *)
  | I.Dec (cQ', MMV (I.MMVar (I.MInst (_, I.Empty, cPsi, tA, _), _s))) ->
      let u = Id.mk_name (Id.MVarName (Typ.gen_var_name tA)) in 
      I.Dec (ctxToMCtx cQ', I.MDecl (u, tA, cPsi))

  | I.Dec (_cQ', MMV (I.MMVar (I.MInst (_, _cD, _cPsi, _tA, _), _s))) ->
      raise (Error leftoverMeta2)

  | I.Dec (cQ', MV (I.MVar (I.Inst (_, cPsi, tA, _), _s))) -> 
      let u = Id.mk_name (Id.MVarName (Typ.gen_var_name tA)) in 
      I.Dec (ctxToMCtx cQ', I.MDecl (u, tA, cPsi)) 

  (* Can this case ever happen?  I don't think so. -bp *)
  | I.Dec (cQ', PV (I.PVar (I.PInst (_, cPsi, tA, _), _s))) -> 
      let p = Id.mk_name (Id.BVarName (Typ.gen_var_name tA)) in   
      I.Dec (ctxToMCtx cQ', I.PDecl (p, tA, cPsi))  

  | I.Dec (cQ', FMV (u, Some (tA, cPsi))) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (u, tA, cPsi)) 

  | I.Dec (cQ', FPV (p, Some (tA, cPsi))) ->
      I.Dec (ctxToMCtx cQ', I.PDecl (p, tA, cPsi))

  (* this case should not happen -bp *)
(* | I.Dec (cQ', FV (_, Some tA)) ->
      I.Dec (ctxToMCtx cQ', I.MDecl (Id.mk_name Id.NoName, tA, I.Null))
*)


(* collectTerm cQ phat (tM,s) = cQ'

   Invariant:

   If  cPsi' |- tM <= tA'   and
       cPsi  |- s  <= cPsi' and  (tM, s) is ins whnf
                            and   phat = |cPsi|
       No circularities in [s]tM
       (enforced by extended occurs-check for FVars
        in Unify (to be done -bp))

   then cQ' = cQ, cQ''
        where cQ'' contains all MVars and FVars in tM
            all MVars and FVars in s are already in cQ.


   Improvement: if tM is in normal form, we don't
                need to call whnf.
*)
let rec collectTerm cQ phat sM = collectTermW cQ phat (Whnf.whnf sM)

and collectTermW cQ ((cvar, offset) as phat) sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      let (cQ', tM') =  collectTerm cQ (cvar, offset + 1) (tM, LF.dot1 s) in 
        (cQ', I.Lam (loc, x, tM'))

  | (I.Tuple (loc, tuple), s) ->
      let (cQ', tuple') = collectTuple cQ phat (tuple, s) in 
        (cQ', I.Tuple (loc, tuple'))

  | (I.Root (loc, h, tS), s) ->
      let (cQ', h') = collectHead cQ phat (h, s) in
      let (cQ'', tS') =  collectSpine cQ' phat (tS, s) in 
        (cQ'', I.Root(loc, h', tS'))

and collectTuple cQ phat = function
  | (I.Last tM, s) -> 
      let (cQ', tM') = collectTerm cQ phat (tM, s) in 
        (cQ', I.Last tM')
  | (I.Cons (tM, tuple), s) ->
      let (cQ', tM') = collectTerm cQ phat (tM, s) in
      let (cQ2, tuple') = collectTuple cQ' phat (tuple, s) in 
        (cQ2, I.Cons(tM', tuple'))


(* collectSpine cQ phat (S, s) = cQ'

   Invariant:
   If    cPsi |- s : cPsi1     cPsi1 |- S : A > P
   then  cQ' = cQ, cQ''
       where cQ'' contains all MVars and FVars in (S, s)

*)
and collectSpine cQ phat sS = match sS with
  | (I.Nil, _) -> (cQ, I.Nil)

  | (I.SClo (tS, s'), s) ->
      collectSpine cQ phat (tS, LF.comp s' s)

  | (I.App (tM, tS), s) ->
    let (cQ', tM') = collectTerm cQ phat (tM, s) in
    let (cQ'', tS') = collectSpine cQ' phat (tS, s) in 
      (cQ'', I.App (tM', tS'))


(* collectSub cQ phat s = cQ'

   Invariant:
   If    cPsi |- s : cPsi1    and phat = |cPsi|
   then  cQ' = cQ, cQ''
   where cQ'' contains all MVars and FVars in s

*)
and collectSub cQ phat s = match s with
  | (I.Shift _) -> (cQ, s)
  | (I.Dot (I.Head h, s)) ->
      let (cQ1, s') =  collectSub cQ phat s in 
      (* let _   = dprint (fun () -> "collectSub (Head) "  ) in *)
      let (cQ2, h') = collectHead cQ1 phat (h, LF.id) in
        (cQ2, I.Dot(I.Head h', s'))

  | (I.Dot (I.Block (h, index), s)) -> 
      let (cQ1, s') =  collectSub cQ phat s in 
      (* let _   = dprint (fun () -> "collectSub (Block) "  ) in *)
      let (cQ2, h') = collectHead cQ1 phat (h, LF.id) in
        (cQ2 , I.Dot (I.Block (h', index), s'))

  | (I.Dot (I.Obj tM, s)) ->
      let (cQ1,s') =  collectSub cQ phat s in 
      (* let _   = dprint (fun () -> "collectSub (term) M = "  ) in
      let _   = dprint (fun () -> "collectSub (term) M = " ^ P.normalToString I.Empty I.Empty (Context.hatToDCtx phat) (tM, LF.id) ) in *)
      let (cQ2, tM') = collectTerm cQ1 phat (tM, LF.id) in
        (cQ2, I.Dot (I.Obj tM', s'))

  | (I.Dot (I.Undef, s')) ->
    (let _ = Printf.printf "Collect Sub encountered undef\n" in 
          collectSub cQ phat  s')


(* collectMSub cQ theta = cQ' *) 
and collectMSub cQ theta =  match theta with 
  | I.MShift _n -> (cQ , theta)
  | I.MDot(I.MObj(phat, tM), t) -> 
      let (cQ1, t') =  collectMSub cQ t in 
      let (cQ2, tM') = collectTerm cQ1 phat (tM, LF.id) in 
        (cQ2 , I.MDot (I.MObj (phat, tM'), t'))

  | I.MDot(I.PObj(phat, h), t) -> 
      let (cQ1, t') =  collectMSub cQ t in 
      let (cQ2, h') = collectHead cQ1 phat (h, LF.id) in 
        (cQ2, I.MDot (I.PObj (phat, h'), t'))

and collectHead cQ phat ((head, _subst) as sH) =
  (* let _ = dprint (fun () -> "###collectHead  "
                          ^ P.normalToString I.Empty I.Empty I.Null (I.Root(None, head, I.Nil), subst)
                          ^ " \ncollection: " ^ collectionToString cQ) in *)
    match sH with

  | (I.BVar _x, _s)  -> (cQ, head)

  | (I.Const _c, _s) -> (cQ, head)

  | (I.FVar name, _s) ->
      if exists (eqFVar name) cQ then
        (cQ, I.FVar name)
      else
        let tA  = FVar.get name in            
        let (cQ', tA') = collectTyp cQ (None, 0) (tA, LF.id) in 
            (* tA must be closed *)
            (* Since we only use abstraction on pure LF objects,
               there are no context variables; different abstraction
               is necessary for handling computation-level expressions,
               and LF objects which occur in computations. *)
            (I.Dec (cQ', FV (name, Some tA')) , I.FVar name)


  | (I.FMVar (u, s'), s) ->
      let (cQ', sigma) = collectSub cQ phat (LF.comp s' s) in
        if exists (eqFMVar u) cQ' then
          (cQ', I.FMVar (u, sigma))
        else
          let (tA, cPhi)  = FMVar.get u in
          let phihat = Context.dctxToHat cPhi in 

          let (cQ1, cPhi')  = collectDctx cQ' phihat cPhi in 
          let (cQ'', tA')   = collectTyp cQ1  phihat (tA, LF.id) in 

            (* tA must be closed with respect to cPhi *)
            (* Since we only use abstraction on pure LF objects,
               there are no context variables; different abstraction
               is necessary for handling computation-level expressions,
               and LF objects which occur in comp utations. *)
            (I.Dec (cQ'', FMV (u, Some (tA', cPhi'))), I.FMVar (u, sigma))

  | (I.MVar (I.Inst (q, cPsi, tA,  ({contents = cnstr} as c)) as r, s') as u, _s) ->
      if constraints_solved cnstr then
        (* let _ = dprint (fun () -> "MVar type " ^ P.typToString I.Empty I.Empty cPsi (tA, LF.id) ) in 
        let _ = dprint (fun () -> "cPsi = " ^ P.dctxToString I.Empty I.Empty cPsi )in
      let _ = dprint (fun () -> "collectSub for MVar \n") in *)
      let (cQ', sigma) = collectSub cQ phat s' in
      (* let _ = dprint (fun () -> "collectSub for MVar done \n") in *)
        if exists (eqMVar u) cQ' then
          (cQ', I.MVar(r, sigma))
        else
          (*  checkEmpty !cnstrs? -bp *)
          let phihat = Context.dctxToHat cPsi in 
          let (cQ1, cPsi')  = collectDctx cQ' phihat cPsi in 
          let (cQ'', tA') = collectTyp cQ1  phihat (tA, LF.id) in 
          let v = I.MVar (I.Inst (q, cPsi', tA',  c), sigma) in 
            (I.Dec (cQ'', MV v) , v)
      else 
        raise (Error "Leftover constraints during abstraction")

  | (I.MMVar (I.MInst (q, I.Empty, cPsi, tA,  ({contents = cnstr} as c)) as r, (ms', s')) as u, _s) ->
      if constraints_solved cnstr then
        let (cQ0, ms1) = collectMSub cQ ms' in 
        let (cQ', sigma) = collectSub cQ0 phat s' in
        if exists (eqMMVar u) cQ' then 
          (cQ', I.MMVar(r, (ms1, sigma)))
        else
          (*  checkEmpty !cnstrs ? -bp *)
          let phihat = Context.dctxToHat cPsi in 
          let (cQ1, cPsi')  = collectDctx cQ' phihat cPsi in 
          let (cQ'', tA') = collectTyp cQ1  phihat (tA, LF.id) in 
          let v = I.MMVar (I.MInst (q, I.Empty, cPsi', tA',  c), (ms1, sigma)) in 
            (I.Dec (cQ'', MMV v) , v)
      else 
        raise (Error "Leftover constraints during abstraction")

  | (I.MMVar (I.MInst (_r, _cD, _cPsi, _tA,  _), _),  _s) ->
      raise (Error leftoverMeta2)

  | (I.MVar (I.Offset k, s'), s) ->
      let (cQ', sigma) = collectSub cQ phat (LF.comp s' s)  in 
        (cQ', I.MVar (I.Offset k, sigma))
      
  | (I.PVar (I.PInst (r, cPsi, tA, ({contents = cnstr} as c)), s') as p,  s) ->
      (*dprint (fun () -> "###abstract  PVar  "
                ^ (match !r with None -> "None" | Some _r -> "Some _")) ; *)
      if constraints_solved cnstr then
        let (cQ', sigma) = collectSub cQ phat (LF.comp s' s) in
          if exists (eqPVar p) cQ' then            
            (cQ', I.PVar (I.PInst (r, cPsi, tA, c), sigma))
          else
            (*  checkEmpty !cnstrs ? -bp *)
            let psihat = Context.dctxToHat cPsi in 
              
            let (cQ1, cPsi')  = collectDctx cQ' psihat cPsi in 
            let (cQ'', tA') = collectTyp cQ1  psihat (tA, LF.id) in              
            let p' = I.PVar (I.PInst (r, cPsi', tA', c), sigma) in 
              (I.Dec (cQ'', PV p') , p')
               
      else 
        raise (Error "Leftover constraints during abstraction")

  | (I.PVar (I.Offset k, s'), _s) ->
      let (cQ', sigma) =  collectSub cQ phat s' (* (LF.comp s' s) *) in 
        (cQ', I.PVar (I.Offset k, sigma))
      
  | (I.FPVar (u, s'), _s) ->
      let (cQ', sigma) = collectSub cQ phat s' (* (LF.comp s' s) *) in
      (* let _ = dprint (fun () -> "###abstract  FPVar  " ^ collectionToString cQ') in *)
        if exists (eqFPVar u) cQ' then
          (cQ', I.FPVar (u, sigma))
        else
          let (tA, cPhi)  = FPVar.get u in
            (* tA must be closed with respect to cPhi *)
            (* Since we only use abstraction on pure LF objects,
               there are no context variables; different abstraction
               is necessary for handling computation-level expressions,
               and LF objects which occur in computations. *)

          let phihat = Context.dctxToHat cPhi in 

          let (cQ1, cPhi')  = collectDctx cQ' phihat cPhi in 
          let (cQ'', tA')   = collectTyp cQ1  phihat (tA, LF.id) in 

            (I.Dec (cQ'', FPV (u, Some (tA', cPhi'))), I.FPVar (u, sigma))

  | (I.Proj (head, k),  s) ->
      (* let _ = dprint (fun () -> "collectHead Proj \n") in  *)
      let (cQ', h') = collectHead cQ phat (head, s)  in
        (cQ' , I.Proj (h', k))


and collectTyp cQ ((cvar, offset) as phat) sA = match sA with
  | (I.Atom (loc, a, tS), s) ->
      let (cQ', tS') = collectSpine cQ phat (tS, s) in 
        (cQ', I.Atom (loc, a, tS'))

  | (I.PiTyp ((I.TypDecl (x, tA), dep ), tB),  s) ->
      let (cQ', tA')  = collectTyp cQ phat (tA, s) in
      let (cQ'', tB') = collectTyp cQ' (cvar, offset + 1) (tB, LF.dot1 s) in
        (cQ'', I.PiTyp ((I.TypDecl (x, tA'), dep ), tB'))

  | (I.TClo (tA, s'),  s) ->
      collectTyp cQ phat (tA, LF.comp s' s)

  | (I.Sigma typRec,  s) ->
      let (cQ', typRec') = collectTypRec cQ phat (typRec, s) in 
        (cQ', I.Sigma typRec')


and collectTypRec cQ ((cvar, offset) as phat) = function
  | (I.SigmaLast tA, s) -> 
      let (cQ', tA') = collectTyp cQ phat (tA, s) in 
        (cQ', I.SigmaLast tA')

  | (I.SigmaElem(loc, tA, typRec), s) ->
       let (cQ',tA') = collectTyp cQ phat (tA, s) in
       let (cQ'', typRec') = collectTypRec cQ' (cvar, offset + 1) (typRec, LF.dot1 s) in 
         (cQ'', I.SigmaElem (loc, tA', typRec'))

and collectKind cQ ((cvar, offset) as phat) sK = match sK with
  | (I.Typ, _s) ->
      (cQ, I.Typ)

  | (I.PiKind ((I.TypDecl (x, tA), dep), tK), s) ->
      let (cQ', tA') = collectTyp cQ phat (tA, s) in
      let (cQ'', tK')= collectKind cQ' (cvar, offset + 1) (tK, LF.dot1 s) in 
        (cQ'', I.PiKind ((I.TypDecl (x, tA'), dep), tK'))


and collectDctx cQ ((cvar, offset) as _phat) cPsi = match cPsi with 
  | I.Null ->  (cQ, I.Null)

  | I.CtxVar _ -> (cQ , cPsi)

  | I.DDec(cPsi, I.TypDecl(x, tA)) ->
      let (cQ', cPsi') =  collectDctx cQ (cvar, offset - 1) cPsi in 
      let (cQ'', tA')  =  collectTyp cQ' (cvar, offset - 1) (tA, LF.id) in 
        (cQ'', I.DDec (cPsi', I.TypDecl(x, tA')))

let rec collectMctx cQ cD = match cD with
  | I.Empty -> (cQ, I.Empty)

  | I.Dec(cD, I.MDecl(u, tA, cPsi)) -> 
      let (cQ', cD')  = collectMctx cQ cD in 
      let phat = Context.dctxToHat cPsi in 
      let (cQ'', cPsi') = collectDctx cQ' phat cPsi in 
      let (cQ2, tA')    =  collectTyp cQ'' phat  (tA, LF.id) in 
        (cQ2, I.Dec(cD', I.MDecl(u, tA', cPsi')))

  | I.Dec(cD, I.PDecl(p, tA, cPsi)) -> 
      let (cQ', cD')  = collectMctx cQ cD in 
      let phat = Context.dctxToHat cPsi in 
      let (cQ'', cPsi') = collectDctx cQ' phat cPsi in 
      let (cQ2, tA')    = collectTyp cQ'' phat (tA, LF.id) in 
        (cQ2,  I.Dec(cD', I.PDecl(p, tA', cPsi')))



(* ****************************************************************** *)
(* Abstraction over LF-bound variables                                *)
(* ****************************************************************** *)

(* abstractKind cQ offset tK = tK'

   where tK' is tK with all occurences of FVar and MVar have been replaced by
   BVar and indexed according to their order in cQ and the base offset

   assumes there are no cycles
*)

let rec abstractKind cQ offset sK = match sK with
  | (I.Typ, _s) -> I.Typ

  | (I.PiKind ((I.TypDecl (x, tA), dep), tK), s) ->
      I.PiKind ((I.TypDecl (x, abstractTyp cQ offset (tA,s)), dep), 
                abstractKind cQ (offset + 1) (tK, LF.dot1 s))

and abstractTyp cQ offset sA = abstractTypW cQ offset (Whnf.whnfTyp sA) 

and abstractTypW cQ offset sA = match sA with
  | (I.Atom (loc, a, tS), s (* id *)) ->
      I.Atom (loc, a, abstractSpine cQ offset (tS, s))

  | (I.PiTyp ((I.TypDecl (x, tA), dep),  tB), s) ->
      I.PiTyp ((I.TypDecl (x, abstractTyp cQ offset (tA, s)), dep), 
               abstractTyp cQ (offset + 1) (tB, LF.dot1 s))


and abstractTypRec cQ offset = function
  | (I.SigmaLast tA, s) -> I.SigmaLast (abstractTyp cQ offset (tA, s))
  | (I.SigmaElem(x, tA, typRec), s) ->
      let tA = abstractTyp cQ offset (tA, s) in
      let typRec = abstractTypRec cQ offset (typRec, LF.dot1 s) in
        I.SigmaElem(x, tA, typRec)



and abstractTerm cQ offset sM = abstractTermW cQ offset (Whnf.whnf sM)

and abstractTermW cQ offset sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      I.Lam (loc, x, abstractTerm cQ (offset + 1) (tM, LF.dot1 s))

  | (I.Root (loc, (I.MVar (I.Inst (_r, cPsi, _tP, _cnstr), s) as tH), _tS (* Nil *)), _s (* LF.id *)) -> 
    (* Since sM is in whnf, _u is MVar (Inst (ref None, tP, _, _)) *)
      let x = index_of cQ (MV tH) + offset in 
        I.Root (loc, I.BVar x, subToSpine cQ offset (s,cPsi) I.Nil)     

  | (I.Root (loc, tH, tS), s (* LF.id *)) ->
      I.Root (loc, abstractHead cQ offset tH, abstractSpine cQ offset (tS, s))


and abstractHead cQ offset tH = match tH with
  | I.BVar x ->
      I.BVar x   

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV (n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise NotImplemented

  (* other cases impossible for object level *)


and subToSpine cQ offset (s,cPsi) tS = match (s, cPsi) with
  | (I.Shift (I.NoCtxShift,_k), I.Null) ->  tS

  | (I.Shift (I.NoCtxShift, k) , I.DDec(_cPsi', _dec)) ->
       subToSpine cQ offset (I.Dot (I.Head (I.BVar (k + 1)), I.Shift (I.NoCtxShift, (k + 1))), cPsi) tS

  | (I.Dot (I.Head (I.BVar k), s), I.DDec(cPsi', I.TypDecl (_, tA))) -> 
      let tN = etaExpandHead None (I.BVar k) (Whnf.normTyp (tA, LF.id)) in 
      subToSpine cQ offset  (s,cPsi') (I.App (tN, tS))

  | (I.Dot (I.Head (I.MVar (_u, _r)), _s) , I.DDec(_cPsi', _dec)) -> 
      (Printf.printf "SubToSpine encountered MVar as head\n";
      raise NotImplemented)
      (* subToSpine cQ offset s (I.App (I.Root (I.BVar k, I.Nil), tS)) *)

  | (I.Dot (I.Obj tM, s), I.DDec(cPsi', _dec)) -> 
      subToSpine cQ offset (s, cPsi') (I.App (abstractTerm cQ offset (tM, LF.id), tS))

and abstractSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractTerm cQ offset (tM,s),  abstractSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractSpine cQ offset (tS, LF.comp s' s)

and abstractCtx cQ =  match cQ with
  | I.Empty ->
      I.Empty

  | I.Dec (cQ, MV (I.MVar (I.Inst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractCtx cQ  in
      let l     = length cPsi in 
      let cPsi' = abstractDctx cQ cPsi l in 
      (* let  (_, depth)  = dctxToHat cPsi in   *)
      (* let tA'   = abstractTyp cQ 0 (tA, LF.id) in *)
      let tA'   = abstractTyp cQ l (tA, LF.id) in 
(*      let _     = Printf.printf "Abstraction: mvar r of type tA = %s\n in context = %s\n with substitution s = %s\n\n"
        (P.typToString I.Empty I.Empty cPsi (tA, LF.id))
        (P.dctxToString I.Empty I.Empty cPsi) 
        (P.subToString I.Empty I.Empty cPsi s) in *)
      let s'    = abstractSub cQ l s in
      let u'    = I.MVar (I.Inst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', MV u')

  | I.Dec (cQ, PV (I.PVar (I.PInst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractCtx cQ  in
      let l     = length cPsi in 
      let cPsi' = abstractDctx cQ cPsi l in 
      (* let  (_, depth)  = dctxToHat cPsi in   *)
      (* let tA'   = abstractTyp cQ 0 (tA, LF.id) in *)
      let tA'   = abstractTyp cQ l (tA, LF.id) in 
      let s'    = abstractSub cQ l s in
      let p'    = I.PVar (I.PInst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', PV p')

  | I.Dec (cQ, FV (f, Some tA)) ->
      let tA' = abstractTyp cQ 0 (tA, LF.id) in
      let cQ' = abstractCtx cQ in
        I.Dec (cQ', FV (f, Some tA'))



and abstractDctx cQ cPsi l = match cPsi with
  | I.Null ->
      I.Null
  | I.CtxVar psi -> I.CtxVar psi

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractDctx cQ cPsi (l-1) in
      let tA'   = abstractTyp cQ (l-1) (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

  (* other cases impossible in LF layer *)

and abstractSub cQ offset s = match s with
  | I.Shift _ ->
      s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractHead cQ offset tH), abstractSub cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractTerm cQ offset (tM, LF.id)), abstractSub cQ offset s)

  (* what about I.Dot (I.Undef, s) ? *)

  (* SVar impossible in LF layer *)

(* ****************************************************************** *)
(* Abstraction over meta-variables and parameter variables            *)
(* ****************************************************************** *)

(* Abstracting over free meta-variables (MVars with references), 
   named free meta-variables, and named free parameter variables to
   create a context cD.


   This is needed in type checking and type reconstruction for computations.

*)

let rec abstractMVarTyp cQ offset sA = abstractMVarTypW cQ offset (Whnf.whnfTyp sA) 

and abstractMVarTypW cQ offset sA = match sA with
  | (I.Atom (loc, a, tS), s (* id *)) ->
      I.Atom (loc, a, abstractMVarSpine cQ offset (tS, s))

  | (I.PiTyp ((I.TypDecl (x, tA), dep), tB), s) ->
      I.PiTyp ((I.TypDecl (x, abstractMVarTyp cQ offset (tA, s)), dep), 
               abstractMVarTyp cQ offset (tB, LF.dot1 s))

  | (I.Sigma typRec,  s) ->
      let typRec'   = abstractMVarTypRec cQ offset (typRec, s) in
        I.Sigma typRec'


and abstractMVarTypRec cQ offset = function
  | (I.SigmaLast tA, s) -> I.SigmaLast (abstractMVarTyp cQ offset (tA, s))
  | (I.SigmaElem(x, tA, typRec), s) ->
      let tA = abstractMVarTyp cQ offset (tA, s) in
      let typRec = abstractMVarTypRec cQ offset (typRec, LF.dot1 s) in
        I.SigmaElem(x, tA, typRec)

and abstractMVarTerm cQ offset sM = abstractMVarTermW cQ offset (Whnf.whnf sM)

and abstractMVarTermW cQ offset sM = match sM with
  | (I.Lam (loc, x, tM), s) ->
      I.Lam (loc, x, abstractMVarTerm cQ offset (tM, LF.dot1 s))

  | (I.Tuple (loc, tuple), s) ->
      I.Tuple (loc, abstractMVarTuple cQ offset (tuple, s))

  | (I.Root (loc, tH, tS), s (* LF.id *)) ->
      I.Root (loc, abstractMVarHead cQ offset tH, abstractMVarSpine cQ offset (tS,s))

and abstractMVarTuple cQ offset = function
  | (I.Last tM, s) ->
      let tM' = abstractMVarTerm cQ offset (tM, s) in
        I.Last tM'
  | (I.Cons (tM, tuple), s) ->
      let tM' = abstractMVarTerm cQ offset (tM, s) in
      let tuple' = abstractMVarTuple cQ offset (tuple, s) in
      I.Cons (tM', tuple')

and abstractMVarHead cQ offset tH = match tH with
  | I.BVar x ->
      I.BVar x

  | I.PVar (I.PInst(_r, _cPsi, _tA , _cnstr), s) -> 
      let x = index_of cQ (PV tH) + offset in 
        I.PVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.FPVar (p, s) -> 
      let x = index_of cQ (FPV (p, None)) + offset in 
        I.PVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MMVar (I.MInst(_r, I.Empty, _cPsi, _tP , _cnstr), (_ms, s)) -> 
      let x = index_of cQ (MMV tH) + offset in 
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MMVar (I.MInst(_r, _cD, _cPsi, _tP , _cnstr), (_ms, _s)) -> 
      raise (Error leftoverMeta2)

  | I.MVar (I.Inst(_r, _cPsi, _tP , _cnstr), s) -> 
      let x = index_of cQ (MV tH) + offset in 
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.MVar (I.Offset x , s) -> 
      I.MVar (I.Offset x, abstractMVarSub cQ offset s) 

  |  I.FMVar (u, s) ->  -> 
      let x = index_of cQ (FMV (u, None)) + offset in 
        I.MVar (I.Offset x, abstractMVarSub cQ offset s)

  | I.Const c ->
      I.Const c

  | I.FVar n ->
      I.BVar ((index_of cQ (FV (n, None))) + offset)

  | I.AnnH (_tH, _tA) ->
      raise NotImplemented

  | I.Proj (head, k) ->
      let head = abstractMVarHead cQ offset head in   (* ??? -jd *)
        I.Proj (head, k)

  | I.PVar (I.Offset p , s) -> 
      I.PVar (I.Offset p, abstractMVarSub cQ offset s)


  (* other cases impossible for object level *)
and abstractMVarSpine cQ offset sS = match sS with
  | (I.Nil, _s) ->
      I.Nil

  | (I.App (tM, tS), s) ->
      I.App (abstractMVarTerm cQ offset (tM,s),  abstractMVarSpine cQ offset (tS, s))

  | (I.SClo (tS, s'), s)  ->
      abstractMVarSpine cQ offset (tS, LF.comp s' s)


and abstractMVarSub cQ offset s = match s with
  | I.Shift _ ->
      s

  | I.Dot (I.Head tH, s) ->
      I.Dot (I.Head (abstractMVarHead cQ offset tH), abstractMVarSub cQ offset s)

  | I.Dot (I.Obj tM, s) ->
      I.Dot (I.Obj (abstractMVarTerm cQ offset (tM, LF.id)), abstractMVarSub cQ offset s)


and abstractMVarDctx cQ offset cPsi = match cPsi with
  | I.Null ->
      I.Null
  | I.CtxVar psi -> I.CtxVar psi

  | I.DDec (cPsi, I.TypDecl (x, tA)) ->
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in
        I.DDec (cPsi', I.TypDecl (x, tA'))

and abstractMVarMctx cQ cD offset = match cD with
  | I.Empty -> I.Empty

  | I.Dec(cD, I.MDecl(u, tA, cPsi)) -> 
      let cD' = abstractMVarMctx cQ cD (offset - 1) in
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in
        I.Dec(cD', I.MDecl (u, tA', cPsi'))

  | I.Dec(cD, I.PDecl(u, tA, cPsi)) -> 
      let cD' = abstractMVarMctx cQ cD (offset - 1) in
      let cPsi' = abstractMVarDctx cQ offset cPsi in
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in
        I.Dec(cD', I.PDecl (u, tA', cPsi'))


and abstractMVarCtx cQ =  match cQ with
  | I.Empty -> I.Empty

  | I.Dec (cQ, MMV (I.MMVar (I.MInst (r, I.Empty, cPsi, tA, cnstr), (ms, s)))) ->
      let cQ'   = abstractMVarCtx  cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in 
      let s'    = abstractMVarSub cQ 0 s in
        (* Do we need to consider the substitution s here? -bp *)  
      let u'    = I.MMVar (I.MInst (r, I.Empty, cPsi', tA', cnstr), (ms, s')) in
        I.Dec (cQ', MMV u')

  | I.Dec (_cQ, MMV (I.MMVar (I.MInst (_r, _cD, _cPsi, _tA, _cnstr), _s))) ->
      raise (Error leftoverMeta2)

  | I.Dec (cQ, MV (I.MVar (I.Inst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractMVarCtx  cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in 
      let s'    = abstractMVarSub cQ 0 s in
        (* Do we need to consider the substitution s here? -bp *)  
      let u'    = I.MVar (I.Inst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', MV u')

  | I.Dec (cQ, PV (I.PVar (I.PInst (r, cPsi, tA, cnstr), s))) ->
      let cQ'   = abstractMVarCtx  cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0  (tA, LF.id) in 
      let s'    = abstractMVarSub cQ 0 s in
        (* Do we need to consider the substitution s here? -bp *)  
      let p'    = I.PVar (I.PInst (r, cPsi', tA', cnstr), s') in
        I.Dec (cQ', PV p')

  | I.Dec (cQ, FMV (u, Some (tA, cPsi))) ->
      let cQ'   = abstractMVarCtx cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in

        I.Dec (cQ', FMV (u, Some (tA', cPsi')))


  | I.Dec (cQ, FPV (u, Some (tA, cPsi))) ->
      let cQ'   = abstractMVarCtx  cQ in
      let cPsi' = abstractMVarDctx cQ 0 cPsi in 
      let tA'   = abstractMVarTyp cQ 0 (tA, LF.id) in

        I.Dec (cQ', FPV (u, Some (tA', cPsi')))


  | I.Dec (_cQ, FV _) ->
        (* This case is hit in e.g.  ... f[g, x:block y:tp. exp unk], where unk is an unknown identifier;
         * is it ever hit on correct code?  -jd 2009-02-12 
         * No. This case should not occur in correct code - bp 
         *)
      raise (Error "abstractMVarCtx(_, FV _): unknown identifier in program?")


(* Cases for: FMV, FPV *)


let rec abstrMSub cQ t = 
  let l = Context.length cQ in 
  let rec abstrMSub' t = 
    match t with
      | I.MShift n -> I.MShift (n+l)
      | I.MDot(I.MObj(phat, tM), t) -> 
          let s'  = abstrMSub' t  in 
          let tM' = abstractMVarTerm cQ 0 (tM, LF.id) in 
            I.MDot(I.MObj(phat, tM'), s') 
              
      | I.MDot(I.PObj(phat, h), t) ->
          let s' = abstrMSub' t in 
          let h' = abstractMVarHead cQ 0 h in 
            I.MDot(I.PObj(phat, h'), s')
  in 
    abstrMSub' t 

and abstractMSub  t =  
  let (cQ, t')  = collectMSub I.Empty t in
  let cQ' = abstractMVarCtx cQ in
  let t''  = abstrMSub cQ' t' in
  let cD'  = ctxToMCtx cQ' in  
    (t'' , cD')  

(*
 and abstractMSub cQ t =  
  let cQ1  = collectMSub cQ t in
  let d    = Context.length cQ in 
  let cQ' = abstractMVarCtx d cQ1 in
  let t'  = abstrMSub cQ' t in
  let cD'  = ctxToMCtx cQ' in  
    (t' , cD')  
*)
(* wrapper function *)
let abstrKind tK =
  (* what is the purpose of phat? *)
  let empty_phat = (None, 0) in
  let (cQ, tK')      = collectKind I.Empty empty_phat (tK, LF.id) in
    begin match cQ with
        Int.LF.Empty -> (tK', 0)
      | _       -> 
          let cQ'        = abstractCtx cQ in
          let tK''        = abstractKind cQ' 0 (tK', LF.id) in
          let cPsi       = ctxToDctx cQ' in
            (raiseKind cPsi tK'', length cPsi)
    end

and abstrTyp tA =
  let empty_phat = (None, 0) in
  let (cQ, tA')       = collectTyp I.Empty empty_phat (tA, LF.id) in
   begin match cQ with 
        Int.LF.Empty -> (Printf.printf "\n Nothing to abstract." ; (tA', 0))
      | _       -> 
          let cQ'        = abstractCtx cQ in
          let tA2        = abstractTyp cQ' 0 (tA', LF.id) in
          let cPsi       = ctxToDctx cQ' in
            begin match raiseType cPsi tA2 with 
              | (None, tA3) -> (tA3, length cPsi)
              | _            -> raise (Error "Abstraction not valid LF-type because of left-over context variable")
            end
    end 

(* *********************************************************************** *)
(* Abstract over computations *)
(* *********************************************************************** *)
let rec collectCompTyp cQ tau = match tau with
  | Comp.TypBox (loc, tA, cPsi) -> 
      let phat = Context.dctxToHat cPsi in 
      let (cQ', cPsi') = collectDctx cQ phat cPsi in 
      let (cQ'', tA')  = collectTyp cQ' phat (tA, LF.id) in 
        (cQ'', Comp.TypBox (loc, tA', cPsi'))

  | Comp.TypArr (tau1, tau2) -> 
      let (cQ1, tau1') = collectCompTyp cQ tau1 in 
      let (cQ2, tau2') = collectCompTyp cQ1 tau2 in 
        (cQ2, Comp.TypArr (tau1', tau2')) 

  | Comp.TypCross (tau1, tau2) -> 
      let (cQ1, tau1') = collectCompTyp cQ tau1 in 
      let (cQ2, tau2') = collectCompTyp cQ1 tau2 in 
        (cQ2, Comp.TypCross (tau1', tau2'))

  | Comp.TypCtxPi (ctx_dec, tau) -> 
      let (cQ1, tau') = collectCompTyp cQ tau  in 
        (cQ1, Comp.TypCtxPi (ctx_dec, tau'))

  | Comp.TypPiBox ((I.MDecl(u, tA, cPsi), dep ), tau) -> 
      let phat = Context.dctxToHat cPsi in 
      let (cQ1, cPsi') = collectDctx cQ phat cPsi in 
      let (cQ2, tA')    = collectTyp cQ1 phat (tA, LF.id) in 
      let (cQ3, tau')  = collectCompTyp cQ2 tau in 
        (cQ3 , Comp.TypPiBox ((I.MDecl(u, tA', cPsi'), dep ), tau'))


let rec collectExp cQ e = match e with 
  | Comp.Syn (loc, i) -> 
      let (cQ', i') = collectExp' cQ i in 
        (cQ', Comp.Syn(loc, i'))

  | Comp.Rec (loc, f, e) -> 
      let (cQ', e') = collectExp cQ e in
        (cQ', Comp.Rec (loc, f, e') )

  | Comp.Fun (loc, x, e) -> 
      let (cQ', e') = collectExp cQ e in 
        (cQ', Comp.Fun (loc, x, e'))

  | Comp.MLam (loc, u, e) -> 
      let (cQ', e') = collectExp cQ e in 
        (cQ', Comp.MLam (loc, u, e'))

  | Comp.Pair (loc, e1, e2) -> 
      let (cQ1, e1') = collectExp cQ e1 in 
      let (cQ2, e2') = collectExp cQ1 e2 in 
        (cQ2, Comp.Pair (loc, e1', e2') )

  | Comp.LetPair (loc, i, (x, y, e)) -> 
      let (cQi, i') = collectExp' cQ i in 
      let (cQ2, e') = collectExp cQi e in 
        (cQ2, Comp.LetPair (loc, i', (x, y, e')))

  | Comp.CtxFun (loc, psi, e) -> 
      let (cQ', e') = collectExp cQ e in 
        (cQ', Comp.CtxFun (loc, psi, e'))

  | Comp.Box (loc, phat, tM) -> 
      let (cQ', tM') = collectTerm  cQ  phat (tM, LF.id)  in 
        (cQ', Comp.Box (loc, phat, tM') )

  | Comp.Case (loc, i, branches) -> 
      let (cQ', i') = collectExp' cQ i in 
      let (cQ2, branches') = collectBranches cQ' branches in 
        (cQ2, Comp.Case (loc, i', branches'))


and collectExp' cQ i = match i with
  | Comp.Var _x -> (cQ , i)
  | Comp.Const _c ->  (cQ , i)
  | Comp.Apply (loc, i, e) -> 
      let (cQ', i') = collectExp' cQ i  in 
      let (cQ'', e') = collectExp cQ' e in 
        (cQ'', Comp.Apply (loc, i', e'))

  | Comp.CtxApp (loc, i, cPsi) -> 
      let (cQ', i') = collectExp' cQ i  in 
      let phat = Context.dctxToHat cPsi in 
      let (cQ'', cPsi') = collectDctx cQ' phat cPsi in 
        (cQ'', Comp.CtxApp (loc, i', cPsi'))

  | Comp.MApp (loc, i, (phat, tM)) -> 
      let (cQ', i') = collectExp' cQ i  in 
      let (cQ'', tM') = collectTerm cQ' phat (tM, LF.id) in 
        (cQ'', Comp.MApp (loc, i', (phat, tM')))

  | Comp.Ann  (e, tau) -> 
      let (cQ', e') = collectExp cQ e in 
      let (cQ'', tau') = collectCompTyp cQ' tau in 
        (cQ'', Comp.Ann  (e', tau'))


and collectPattern cQ cD cPsi (phat, tM) tA = 
  let (cQ1, cD') = collectMctx cQ cD in 
  (* let _    = Printf.printf "Start Collection of cPsi = %s\n" 
  (   P.dctxToString cPsi) in  *)
  let (cQ2, cPsi') = collectDctx cQ1 phat cPsi in 
  (* let _ = Printf.printf "cQ2 (collection of cPsi)\n" in 
     let _   = printCollection cQ2 in  *)
  let (cQ3, tM') = collectTerm cQ2 phat (tM, LF.id) in 
  (* let _ = Printf.printf "cQ3 (collection of cPsi)\n" in 
     let _   = printCollection cQ3 in  *)
  let (cQ4, tA') = collectTyp cQ3 phat (tA, LF.id) in 
  (* let _ = Printf.printf "cQ4 (collection of cPsi)\n" in 
  let _   = printCollection cQ4 in  *)
    (cQ4, cD', cPsi', (phat, tM'), tA')




and collectBranch cQ branch = match branch with
  | Comp.BranchBox (cD, pat, e) -> 
      (* pat and cD cannot contain any free meta-variables *)
      let (cQ', e') =  collectExp cQ e in 
        (cQ', Comp.BranchBox (cD, pat, e') )

and collectBranches cQ branches = match branches with 
  | [] -> (cQ, [])
  | b::branches -> 
      let (cQ', b') = collectBranch cQ b in
      let (cQ2, branches') =  collectBranches cQ' branches in 
        (cQ2, b'::branches')


let rec abstractMVarCompTyp cQ offset tau = match tau with 
  | Comp.TypBox (loc, tA, cPsi) -> 
      let cPsi' = abstractMVarDctx cQ offset cPsi in 
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in 
        Comp.TypBox (loc, tA', cPsi')      

  | Comp.TypArr (tau1, tau2) -> 
      Comp.TypArr (abstractMVarCompTyp cQ offset tau1, 
                   abstractMVarCompTyp cQ offset tau2)

  | Comp.TypCross (tau1, tau2) -> 
      Comp.TypCross (abstractMVarCompTyp cQ offset tau1, 
                     abstractMVarCompTyp cQ offset tau2)

  | Comp.TypCtxPi (ctx_decl, tau) -> 
      Comp.TypCtxPi (ctx_decl, abstractMVarCompTyp cQ offset tau)

  | Comp.TypPiBox ((I.MDecl(u, tA, cPsi), dep), tau) -> 
      let cPsi' = abstractMVarDctx cQ offset cPsi in 
      let tA'   = abstractMVarTyp cQ offset (tA, LF.id) in 
      let tau'  = abstractMVarCompTyp cQ (offset+1) tau in 
        Comp.TypPiBox ((I.MDecl(u, tA', cPsi'), dep), tau')

(* REDUNDANT Tue Apr 21 09:50:08 2009 -bp 
let rec abstractMVarExp cQ offset e = match e with
  | Comp.Syn (loc, i) -> Comp.Syn (loc, abstractMVarExp' cQ offset i)

  | Comp.Rec (loc, f, e) -> Comp.Rec (loc, f, abstractMVarExp cQ offset e)

  | Comp.Fun (loc, x, e) -> Comp.Fun (loc, x, abstractMVarExp  cQ offset e)

  | Comp.MLam (loc, u, e) -> Comp.MLam (loc, u, abstractMVarExp  cQ (offset+1) e)

  | Comp.Pair (loc, e1, e2) -> 
      let e1' = abstractMVarExp  cQ offset e1 in 
      let e2' = abstractMVarExp  cQ offset e2 in 
        Comp.Pair (e1', e2')

  | Comp.LetPair (loc, i, (x, y, e)) -> 
      let i' = abstractMVarExp' cQ offset i in 
      let e' = abstractMVarExp cQ offset e in 
        Comp.LetPair (loc, i', (x, y, e'))

  | Comp.CtxFun (loc, psi, e) -> Comp.CtxFun (loc, psi, abstractMVarExp cQ offset e)

  | Comp.Box (loc, phat, tM) -> Comp.Box (loc, phat, abstractMVarTerm  cQ  offset (tM, LF.id) )

  | Comp.Case (loc, i, branches) -> 
      let i' = abstractMVarExp' cQ offset i in 
        Comp.Case(loc, i', abstractMVarBranches cQ offset branches)


and abstractMVarExp' cQ offset i = match i with
  | Comp.Var x -> Comp.Var x 
  | Comp.Const _c ->  i
  | Comp.Apply (loc, i, e) -> 
      let i' = abstractMVarExp' cQ offset i  in 
      let e' = abstractMVarExp  cQ offset e in 
        Comp.Apply (loc, i', e')

  | Comp.CtxApp (loc, i, cPsi) -> 
      let i' = abstractMVarExp' cQ offset i  in 
      let cPsi' = abstractMVarDctx cQ offset cPsi in 
        Comp.CtxApp (loc, i', cPsi')

  | Comp.MApp (loc, i, (phat, tM)) -> 
      let i' = abstractMVarExp' cQ offset i  in 
      let tM' = abstractMVarTerm cQ offset (tM, LF.id) in
        Comp.MApp (loc, i', (phat, tM'))

  | Comp.Ann  (e, tau) -> 
      let e' = abstractMVarExp cQ offset e in 
      let tau' = abstractMVarCompTyp cQ offset tau in 
        Comp.Ann (e', tau')

and abstractMVarBranches cQ offset branches = 
  List.map (function b -> abstractMVarBranch cQ offset b) branches

and abstractMVarBranch cQ offset branch = match branch with 
  | Comp.BranchBox(cD, (cPsi, tM, (t, cD')), e) ->     
      (* cD, tM, tA, cPsi cannot contain any free meta-variables *)
      let offset  = Context.length cD + offset in 
      let e'      = abstractMVarExp  cQ offset e in 
        Comp.BranchBox (cD, (phat, tM, (tA, cPsi)), e')

*)

let raiseCompTyp cD tau = 
  let rec roll tau = match tau with
    | Comp.TypCtxPi (ctx_decl, tau) -> 
        Comp.TypCtxPi (ctx_decl, roll tau)
    | tau -> raisePiBox cD tau 

  and raisePiBox cD tau = match cD with
    | I.Empty -> tau
    | I.Dec(cD ,mdecl) -> 
        raisePiBox cD (Comp.TypPiBox ((mdecl, Comp.Implicit), tau))
  in 
    roll tau 


let raiseExp cD e = 
  let rec roll e = match e with
    | Comp.CtxFun (loc, psi, e) -> 
        Comp.CtxFun (loc, psi, roll e)
    | e -> raiseMLam cD e 

  and raiseMLam cD e = match cD with
    | I.Empty -> e
    | I.Dec(cD ,I.MDecl(u, _cPsi, _tA)) -> 
        raiseMLam cD (Comp.MLam (None, Id.mk_name (Id.SomeName u), e))
  in 
    roll e


let rec abstrCompTyp tau = 
  let (cQ, tau1)  = collectCompTyp I.Empty tau in 
  let cQ'  = abstractMVarCtx cQ in 
  let tau' = abstractMVarCompTyp cQ' 0 tau1 in 
  let cD'  = ctxToMCtx cQ' in 
    (raiseCompTyp cD' tau', Context.length cD')


(*  
   1) Collect FMVar and FPVars  in cD1, Psi1, tM and tA
   2) Abstract FMVar and FPVars in cD1, Psi1, tM and tA
 
*)
let rec abstrPattern cD1 cPsi1  (phat, tM) tA =  
  let (cQ, cD1', cPsi1', (phat, tM'), tA')  = collectPattern I.Empty cD1 cPsi1 (phat,tM) tA in
  let cQ'     = abstractMVarCtx cQ in 
  let offset  = Context.length cD1' in 
  let cPsi2  = abstractMVarDctx cQ' offset cPsi1' in 
  let tM2     = abstractMVarTerm cQ' offset (tM', LF.id) in
  let tA2     = abstractMVarTyp  cQ' offset (tA', LF.id) in 
  let cD2    = abstractMVarMctx cQ' cD1' (offset-1) in 
  let cD'     = ctxToMCtx cQ' in 
  let cD      = Context.append cD' cD2 in 
    (cD, cPsi2, (phat, tM2), tA2)
    


let rec abstrExp e =
  let (cQ, e')    = collectExp I.Empty e in 
    begin match cQ with 
        I.Empty -> e'
      | _       -> ((* Printf.printf "Impossible? Leftover free MVars-ref that are not already constrained?\n";*)
                      raise (Error "Abstract: Encountered free MVars in computation-level expression"))
    end

(* appDCtx cPsi1 cPsi2 = cPsi1, cPsi2 *)
let rec appDCtx cPsi1 cPsi2 = match cPsi2 with
  | I.Null -> cPsi1
  | I.DDec (cPsi2', dec) ->
      let cPsi1' = appDCtx cPsi1 cPsi2' in 
        I.Dec (cPsi1', dec)

let rec abstrSchema (I.Schema elements) = 
  let rec abstrElems elements = match elements with
    | [] -> []
    | Int.LF.SchElem (cPsi, trec) ::els ->         
        let cPsi0 = Context.projectCtxIntoDctx cPsi in 
        let (cQ, cPsi0') = collectDctx I.Empty (Context.dctxToHat I.Null) cPsi0 in 
        let (_, l) as phat = Context.dctxToHat cPsi0 in 
        let (cQ, trec') = collectTypRec cQ phat (trec, LF.id) in 
        let cQ' = abstractCtx cQ in 

        let cPsi' = abstractDctx cQ' cPsi0'  l in 
        let trec' = abstractTypRec cQ' l (trec', LF.id) in 
        let cPsi1 = ctxToCtx cQ' in 
        let cPsi1' = appDCtx cPsi1 cPsi' in 

        let els'  = abstrElems els in 
          Int.LF.SchElem (cPsi1', trec') :: els'         
  in 
    I.Schema (abstrElems elements)


(* REDUNDANT Tue Apr 21 09:52:37 2009 -bp 
let rec abstrBranch (cPsi1, (phat, tM), tA) e r =  
  let cQ0     = collectPattern I.Empty I.Empty cPsi1 (phat,tM) tA in
  let cQ1     = collectExp cQ0 e in 
  let cQ2     = collectMSub cQ1 r in 
  let cQ'     = abstractMVarCtx cQ2 in 

  let cPsi1'  = abstractMVarDctx cQ' 0 cPsi1 in 
  let tM'     = abstractMVarTerm cQ' 0 (tM, LF.id) in
  let tA'     = abstractMVarTyp  cQ' 0 (tA, LF.id) in 
  
  let e'      = abstractMVarExp cQ' 0 e in 

  let r'      = abstrMSub cQ' r in 
  let cD      = ctxToMCtx cQ' in 
    (cD, (cPsi1', (phat, tM'), tA'), e', r')

*)

(* let rec abstrExpMSub e t =
  let cQ1     = collectMSub I.Empty t in
  let cQ      = collectExp cQ1 e in 
  let cQ'     = abstractMVarCtx cQ in 
  let e'      = abstractMVarExp cQ' 0 e in 
  let t'      = abstrMSub cQ' t in
  let cD'     = ctxToMCtx cQ' in 
     (cD', t', e')
*)


let rec printFreeMVars phat tM = 
  let (cQ, _ ) = collectTerm I.Empty  phat (tM, LF.id) in 
    printCollection cQ


let collectTerm' (phat, tM ) = collectTerm I.Empty  phat (tM, LF.id) 
