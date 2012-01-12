(** Coverage checker

   @author Brigitte Pientka
*)

(* open Id *)

open Syntax.Int
open Syntax.Int.Comp

module Types = Store.Cid.Typ
module Const = Store.Cid.Term

module S = Substitution
module U = Unify.EmptyTrail
module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.NamedRenderer

let idSub  = S.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)
let idMSub = Whnf.m_id
let idCSub = LF.CShift 0

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [29])

let printOptionalLocation locOpt = match locOpt with
        | None     -> Format.fprintf Format.std_formatter "<unknown location>"
        | Some loc -> Parser.Grammar.Loc.print Format.std_formatter loc

(* Generating meta-variable and parameter variable names,
 *  e.g. for Obj-no-split (MVars)
 *)
let counter = ref 0

let new_parameter_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (string ^ string_of_int !counter))

let new_bvar_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (string ^ string_of_int !counter))

let new_name string =
   new_parameter_name (String.uppercase string)

(* ****************************************************************************** *)
(* Coverage problem *)

type problem = {loc : Parser.Grammar.Loc.t;    
                prag : Pragma.case_pragma;           (* indicates if %not appeared after ``case...of'' *)
                cO : LF.mctx;
                cD : LF.mctx;
                branches : Comp.branch list;
                ctype : (LF.typ * LF.dctx)}         (* type and context of scrutinee *)

(* Make a coverage proble *)
let make loc prag cO cD branches cA =
  {loc= loc;
   prag= prag;
   cO= cO;
   cD= cD;
   branches= branches;
   ctype = cA}

(* Final Coverage Result *)
type coverage_result =
  | Success
  | Failure of (unit -> string)

exception NoCover of (unit -> string)
exception Cover 

(* ****************************************************************************** *)
(* Rigid matching  algorithm : pre-matching algorithm which will generate 
   candidates*)

type depend   = Atomic | Dependent

type cov_goal =  CovGoal of LF.dctx * LF.normal * LF.tclo
                            (*  cPsi |- tR <= sP *)
 
type pattern = 
    NeutPatt  of  LF.dctx * LF.normal * LF.tclo
  | EmptyPatt of  LF.dctx * LF.tclo

type eqn   = Eqn of cov_goal * pattern | EqnCtx of LF.dctx * LF.dctx 

type split = Split of cov_goal * pattern | SplitCtx of LF.dctx * LF.dctx 

type candidate = 
    Cand of  (LF.mctx * LF.mctx) *          (* meta-context of pattern                 *) 
              eqn list * split list 

type candidates = candidate list

type cov_problem =  
    CovCTerm of (LF.mctx * LF.mctx) *   (* meta-context of cov_goal                *) 
                candidates *            (* candidats = (Eqns , Splits)             *)
		(LF.dctx * LF.normal)   (* current coverage goal being considered  *)
  | CovCtx of  (LF.mctx * LF.mctx) *    (* meta-context of cov_goal                *) 
                candidates *            (* candidats = (Eqns , Splits)             *)
		LF.dctx                 (* current coverage goal being considered  *)

type cov_problems = cov_problem list


let open_cov_goals  = ref ([]   :  ((LF.mctx * LF.mctx) * LF.dctx * LF.normal) list )

let reset_cov_problem () = open_cov_goals := [] 

type solved = Solved | NotSolvable | PossSolvable of candidate

type refinement_candidate = 
  | TermCandidate of ((LF.mctx * LF.mctx) * cov_goal * LF.msub)  
  | CtxCandidate of ((LF.mctx * LF.mctx) * LF.dctx * LF.csub * LF.msub) 

type refinement_cands = 
    NoCandidate
  | SomeTermCands of depend * (refinement_candidate list)
  | SomeCtxCands of refinement_candidate list


let rec lower cPsi sA = match sA with 
  | (LF.Atom (_ , a, _tS), s) -> (cPsi , Whnf.whnfTyp sA)
  | (LF.PiTyp ((decl, _ ), tB), s) -> lower (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s)


(* etaExpandMVstr cPsi sA  = tN
 *
 *  cPsi   |- [s]A <= typ
 *  cPsi   |- ss  <= cPsi' 
 *  cPsi'  |- tN   <= [s'][s]A
 *)


let rec etaExpandMVstr cO cPsi sA  = etaExpandMVstr' cO cPsi (Whnf.whnfTyp sA)  

and etaExpandMVstr' cO cPsi sA  = match sA with
  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cPsi in  
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let tQ    = ConvSigma.strans_typ (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

      let (ss', cPhi') = Subord.thin' cO a cPhi in  
      (* cPhi |- ss' : cPhi' *)
      let ssi' = S.LF.invert ss' in
      (* cPhi' |- ssi : cPhi *) 
      (* cPhi' |- [ssi]tQ    *)
      let u = Whnf.newMVar (cPhi', LF.TClo(tQ,ssi')) in
      (* cPhi |- ss'    : cPhi' 
         cPsi |- s_proj : cPhi 
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = S.LF.comp ss' s_proj in 
        LF.Root (Syntax.Loc.ghost, LF.MVar (u, ss_proj), LF.Nil)   

  | (LF.PiTyp ((LF.TypDecl (x, _tA) as decl, _ ), tB), s) ->
      LF.Lam (Syntax.Loc.ghost, x, etaExpandMVstr cO (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s) )

    

(*
(* etaExpandMVstr cPsi sA  = tN
 *
 *  cPsi   |- [s]A <= typ
 *  cPsi   |- ss  <= cPsi' 
 *  cPsi'  |- tN   <= [s'][s]A
 *)


let rec etaExpandMVstr cO cPsi sA  = etaExpandMVstr' cO cPsi (Whnf.whnfTyp sA)  

and etaExpandMVstr' cO cPsi sA  = match sA with
  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (ss', cPsi') = Subord.thin' cO a cPsi in 
      (* cPsi |- ss' : cPsi' *)
      let ssi' = S.LF.invert ss' in
      (* cPsi' |- ssi : cPsi *) 
      let s0 = S.LF.comp s ssi' in 
      (*  cPsi0 |- tP   and cPsi |- s : cPsi0
          cPsi' |- comp s ss1 <= cPsi0
      *)
      let u = Whnf.newMVar (cPsi', LF.TClo(tP,s0)) in
        LF.Root (Syntax.Loc.ghost, LF.MVar (u, ss'), LF.Nil)  

  | (LF.PiTyp ((LF.TypDecl (x, _tA) as decl, _ ), tB), s) ->
      LF.Lam (None, x, etaExpandMVstr cO (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s) )
*)

(*
 Example: 

 X:nat 
 |-  Cand ( Null  ,  [] , [ X = z ] ), 
     Cand ( N:nat ,  [],  [ X = suc N ] ), 

*)

let rec mvlistToString mvlist = match mvlist with
  | [] -> ""
  | LF.Offset k :: []  -> string_of_int k
  | LF.Offset k :: mvl -> string_of_int k ^ " , " ^ mvlistToString mvl


let rec cvlistToString cvlist = match cvlist with
  | [] -> ""
  | LF.CtxOffset k :: []  -> string_of_int k
  | LF.CtxOffset k :: cvl -> string_of_int k ^ " , " ^ cvlistToString cvl


let rec pattToString cD patt = match patt with
  | NeutPatt (cPsi, tR, sA) -> 
      P.dctxToString cD cPsi ^ " . " ^ 
      P.normalToString cD cPsi (tR, S.LF.id) ^ " : " ^ P.typToString cD cPsi sA 
  | EmptyPatt (cPsi, sA) -> 
           P.dctxToString cD cPsi ^ " . " ^ "     ()    : " ^ P.typToString cD cPsi sA 


let rec covGoalToString (cO, cD) cg = 
  let CovGoal(cPsi, tR, sA) = cg in 
    P.dctxToString cD cPsi ^ " . " ^ 
    P.normalToString cD cPsi (tR, S.LF.id) ^ " : " ^ P.typToString cD cPsi sA 

let rec covGoalsToString cov_goals = match cov_goals with 
  | [] -> "\n"
  | ((cO,cD), cg, _ ) :: cgoals -> 
      covGoalToString (cO, cD) cg ^ "\n     " ^  covGoalsToString  cgoals 

let rec splitsToString (cO, cD) ((_, cD_p) as cOD_p) splits = match splits with 
  | [] -> "\n"
  | (Split (cg, patt) :: splits ) ->       
      covGoalToString (cO, cD) cg ^ " == " ^ pattToString cD_p patt ^ "\n   " ^ splitsToString (cO, cD) cOD_p splits
  | (SplitCtx (cPsi, cPhi) :: splits ) -> 
      let (cO_p, cD_p) = cOD_p in 
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    " ^  splitsToString (cO, cD) cOD_p splits

let rec eqnsToString (cO, cD) ((_, cD_p) as cOD_p) eqns = match eqns with 
  | [] -> "\n"
  | (Eqn (cg, patt) :: eqns ) -> 
      covGoalToString (cO, cD) cg ^ " == " ^ pattToString cD_p patt ^ "\n   " ^ eqnsToString (cO, cD) cOD_p eqns
  | (EqnCtx (cPsi, cPhi) :: splits ) -> 
      let (cO_p, cD_p) = cOD_p in 
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    " ^  eqnsToString (cO, cD) cOD_p splits


let rec candToString (cO,cD) (Cand ((cO_p, cD_p) as cOD_p, eqns, splits)) = 
	 P.mctxToString cD     ^ " ; \n"  ^
	 P.mctxToString cD_p ^ " \n   |- \n" ^ 
	 " MATCHES { \n    " ^ eqnsToString (cO, cD) (cOD_p) eqns ^ "         }\n" ^ 
	 " SPLITS { \n    " ^ splitsToString (cO, cD) (cOD_p) splits ^ "          }\n]\n" 


let rec candidatesToString' (cO, cD) candidates k = match candidates with  
  | [] -> "\n\n"
  | (Cand ((cO_p, cD_p) as cOD_p, eqns, splits) :: cands) -> 
       "[CANDIDATE " ^ string_of_int k ^ " : \n" ^ 
	 P.mctxToString cD     ^ " ; \n"  ^
	 P.mctxToString cD_p ^ " \n   |- \n" ^ 
	 " MATCHES { \n    " ^ eqnsToString (cO, cD) (cOD_p) eqns ^ "         }\n" ^ 
	 " SPLITS { \n    " ^ splitsToString (cO, cD) (cOD_p) splits ^ "          }\n]\n" ^ 
	 candidatesToString' (cO, cD)  cands (k+1)

let candidatesToString ((cO, cD), candidates, (cPsi,tM) ) = 
"COVERAGE GOAL : " ^ 
P.mctxToString cD ^ " ; " ^ P.dctxToString cD cPsi ^ "\n   |-  \n" ^ 
P.normalToString cD cPsi (tM, S.LF.id) ^ "\nCOVERED BY\n" ^ 
candidatesToString' (cO, cD) candidates 1

let rec covproblemsToString cov_problems = match cov_problems with
  | [] -> "\n"
  | cov_prob :: cov_probs -> 
      candidatesToString cov_prob ^ "\n   " ^ covproblemsToString cov_probs


let rec goalsToString ogoals k = match ogoals with 
  | [] -> ""
  | ((cO,cD), cPsi, tM) :: ogoals -> 
      "\n(" ^ string_of_int k ^ ")   " ^ 
        P.mctxToString cD ^ "\n " ^ 
	P.dctxToString cD cPsi ^ "\n   |-  " ^
	P.normalToString cD cPsi (tM, S.LF.id) ^ "\n" ^ 
	goalsToString ogoals (k+1) 


let rec opengoalsToString ogoals = goalsToString ogoals 1


(* ****************************************************************************** *)

exception Error of string
exception NewCandidate of eqn list * split 

(* Assumes that tA[Psi] is an instance of tA'[cPsi'], i.e.
   pre-matching for contextual types suceeded.
*)

exception MatchError of string
exception NothingToRefine


type result = Yes of LF.tclo * LF.tclo | Inst | SplitCand | No
			
let rec pre_match_head (cPsi, tH) (cPsi', tH') = match (tH , tH') with 
  | (LF.BVar k , LF.BVar k') -> 
      if k = k' then 
	let LF.TypDecl (_x, tA )  = Context.ctxDec cPsi  k  in 
	let LF.TypDecl (_y, tA') = Context.ctxDec cPsi' k' in 
	  Yes ((tA,idSub), (tA', idSub)) 
      else No
  | (LF.PVar _ , LF.BVar k)  -> SplitCand
  | (LF.BVar k , LF.PVar _ ) -> Inst 
  | (LF.PVar _ , LF.PVar _ ) -> Inst 

  | (LF.Const c, LF.Const c') ->  
      if c = c' then 
	let tA  = (Const.get c ).Const.typ   in 
	  Yes ((tA,idSub), (tA,idSub)) 
      else No

  | (LF.Const c, LF.PVar _ ) -> No
  | (LF.Const c, LF.BVar _ )   -> No
  | (LF.Const c, LF.Proj (_, _ ) ) -> No

  | (LF.Proj (LF.BVar k, j), LF.Proj (LF.BVar k', j')) -> 
    if k = k' && j = j' then 
	let LF.TypDecl (_ , tA )  = Context.ctxDec cPsi  k  in 
	let LF.TypDecl (_ , tA')  = Context.ctxDec cPsi' k' in 
	  Yes ((tA,idSub), (tA',idSub)) 
    else No
  | (LF.Proj (LF.PVar _ , j)  , LF.Proj (LF.BVar k', j'))  -> 
      if j == j' then SplitCand else No
  | (LF.Proj (LF.BVar k , j)  , LF.Proj (LF.PVar _ , j'))  -> 
      if j == j' then Inst  else No
  | (LF.Proj (LF.PVar _ , j)  , LF.Proj (LF.PVar _ , j'))  -> 
      if j == j' then Inst else No

  | (LF.MVar _ , LF.MVar _ ) -> Inst 
  | (_         , LF.MVar  _ ) -> Inst
  | (LF.MVar _ ,  _         ) -> SplitCand 

  | (LF.PVar _ , LF.Const _) -> No
  | (LF.PVar _ , LF.Proj (_ , _ ) )-> No
  | (LF.Proj ( _, _ ) , LF.Const _ ) -> No
  | (LF.Proj ( _, _ ) , LF.BVar _ ) -> No
  | (LF.Proj ( _, _ ) , LF.PVar _ ) -> No
  | ( _ , _ ) -> No
 
(* pre_match (cPsi,tM, tA) (cPsi', tM', tA') matchCands splitCands = (matchCands', splitCands')

   if cD ; cPsi |- tM  <= tA 
      cD ; cPsi |- tM' <= tA
   then
      matchCands' is an extension of matchCands containing 
       atomic equations which need to be solved for tM to be an instance of tM'

      splitCands' is an extension of splitCands containing
       atomic splitting candidates, i.e. where tM and tM' currently disagree


   Effect: pre_match may raise an exception MatchError, if tM can never be an
   instance of tM' and splitting is not able to make any progress.
 
 *)
let rec pre_match cOD cOD_p covGoal patt matchCands splitCands = 

  let CovGoal (cPsi, tM, sA ) = covGoal in 
  let NeutPatt(cPhi, tN, sA') = patt in 

  begin match  (tM, tN)  with 
    | (LF.Lam (_ , x, tM) , LF.Lam (_, _y, tN)) -> 

	let (LF.PiTyp((tdecl , _ ), tB ), s ) = Whnf.whnfTyp sA in 
	let (LF.PiTyp((tdecl', _ ), tB'), s') = Whnf.whnfTyp sA' in 

	let covGoal' = CovGoal (LF.DDec (cPsi, S.LF.decSub tdecl s), 
				 tM, (tB, S.LF.dot1 s) ) in 
	let patt'    = NeutPatt (LF.DDec (cPhi, S.LF.decSub tdecl' s'), 
				 tN, (tB', S.LF.dot1 s')) in 

	  pre_match cOD cOD_p covGoal' patt' matchCands splitCands

    | (LF.Root (_ , tH, tS), LF.Root (_, tH', tS')) -> 
	begin match pre_match_head (cPsi, tH) (cPhi, tH') with 
	  | Yes (sA, sA') -> 	  
	      pre_match_spine  cOD cOD_p 
		               (cPsi , tS , sA)  
		               (cPhi , tS', sA')
		               matchCands splitCands
	  | No            -> raise (MatchError "Head mismatch")
	  | Inst          -> 
	      (Eqn (covGoal, patt) :: matchCands , splitCands)
	  | SplitCand     -> (matchCands , Split (covGoal, patt)::splitCands)
	end
  end

and pre_match_spine cOD cOD_p (cPsi , tS , sA)
                              (cPsi', tS', sA') matchCands splitCands = 
  begin match (tS, tS') with
    | (LF.Nil , LF.Nil) -> (matchCands, splitCands)
    | (LF.App (tM, tS) , LF.App (tM', tS')) -> 

	let (LF.PiTyp((LF.TypDecl(_x, tB1) , _ ), tB2 ), s)  = Whnf.whnfTyp sA in 
	let (LF.PiTyp((LF.TypDecl(_y, tC1) , _ ), tC2 ), s') = Whnf.whnfTyp sA' in 

	let covGoal1  = CovGoal  (cPsi , tM , (tB1,s)) in 
	let patt1     = NeutPatt (cPsi', tM', (tC1,s')) in 

        let sB2' = (tB2, LF.Dot(LF.Obj(tM ), s)) in 
        let sC2' = (tC2, LF.Dot(LF.Obj(tM'), s')) in 

	let (matchCands', splitCands') = pre_match cOD cOD_p covGoal1 patt1 matchCands splitCands in 

	  pre_match_spine cOD cOD_p (cPsi , tS , sB2')
                                    (cPsi', tS', sC2') matchCands' splitCands'
  end

let rec pre_match_typ cOD cOD_p (cPsi, sA) (cPhi, sB) matchCands splitCands = 
  let _ = dprint (fun () -> 
		    let (cO, cD) = cOD in 
		    let (cO', cD') = cOD_p in 
		      "[pre_match_typ] sA = " ^ P.typToString cD cPsi sA ^ "\n" ^ 
		      "                sB = " ^ P.typToString cD' cPhi sB) in 
    match (Whnf.whnfTyp sA , Whnf.whnfTyp sB) with 
  | (LF.Atom (_, a, tS1) , s1) , (LF.Atom (_, b, tS2), s2) -> 
      let tK1 = (Types.get a).Types.kind in
      let tK2 = (Types.get b).Types.kind in
      let tS1' = Whnf.normSpine (tS1, s1) in 
      let tS2' = Whnf.normSpine (tS2, s2) in 
	if a = b then 
	  pre_match_typ_spine cOD cOD_p (cPsi, tS1', (tK1, S.LF.id)) (cPhi, tS2', (tK2, S.LF.id))
                              matchCands splitCands
	else raise (MatchError "Type Head mismatch")
  | (LF.PiTyp ((LF.TypDecl(x, tA1), _ ), tA2), s1) ,  (LF.PiTyp ((LF.TypDecl(y, tB1), _ ), tB2), s2) -> 
      let (matchCands' , splitCands') = pre_match_typ cOD cOD_p (cPsi, (tA1, s1)) (cPhi, (tB1, s2)) 
	                                              matchCands splitCands
      in 
	pre_match_typ cOD cOD_p (LF.DDec (cPsi, LF.TypDecl (x, LF.TClo (tA1, s1))), (tA2, S.LF.dot1 s1))
                                (LF.DDec (cPhi, LF.TypDecl (y, LF.TClo (tB1, s1))), (tB2, S.LF.dot1 s2))
         	      matchCands' splitCands'

  | (LF.Sigma trec1 , s1) , (LF.Sigma trec2, s2) -> 
      pre_match_trec cOD cOD_p cPsi cPhi (trec1, s1) (trec2, s2) 
	matchCands splitCands

      

and pre_match_trec cOD cOD_p cPsi cPhi srec1 srec2 matchCands splitCands = match (srec1, srec2) with
  | (LF.SigmaLast tA1, s1)  , (LF.SigmaLast tA2, s2) -> 
      pre_match_typ cOD cOD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands
  | (LF.SigmaElem (x1, tA1, trec1) , s1) , (LF.SigmaElem (x2, tA2, trec2) , s2) -> 
      let (mC, sC) = pre_match_typ cOD cOD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands in 
	pre_match_trec cOD cOD_p (LF.DDec(cPsi, LF.TypDecl(x1, LF.TClo(tA1,s1)))) (LF.DDec(cPhi, LF.TypDecl(x2, LF.TClo(tA2,s2))))
	  (trec1, S.LF.dot1 s1) (trec2, S.LF.dot1 s2) 
	  mC sC

and pre_match_typ_spine cOD cOD_p (cPsi, tS1, sK1) (cPsi', tS2, sK2) 
                       matchCands splitCands = 
  begin match ((tS1,sK1), (tS2, sK2)) with
    | (LF.Nil, (LF.Typ, _ )) , (LF.Nil, (LF.Typ, _ )) -> (matchCands, splitCands)
    | (LF.App (tM, tS), sK) , (LF.App (tM', tS') , sK')-> 

	let (LF.PiKind((LF.TypDecl(_x, tB) , _ ), tK1 ), s)  = sK in 
	let (LF.PiKind((LF.TypDecl(_y, tC) , _ ), tK2 ), s') = sK' in 

	let covGoal1  = CovGoal  (cPsi , tM , (tB,s)) in 
	let patt1     = NeutPatt (cPsi', tM', (tC,s')) in 

        let sK1' = (tK1, LF.Dot(LF.Obj(tM ), s)) in 
        let sK2' = (tK2, LF.Dot(LF.Obj(tM'), s')) in 

	let (matchCands', splitCands') = pre_match cOD cOD_p covGoal1 patt1 matchCands splitCands in 

	  pre_match_typ_spine cOD cOD_p (cPsi , tS , sK1')
                                        (cPsi', tS', sK2') matchCands' splitCands'
  end
 


let rec pre_match_dctx cOD cOD_p cPsi cPhi_patt matchCands splitCands = 
  let _ = dprint (fun () -> let (cO, cD) = cOD in 
		  let (cO', cD') = cOD_p in 
		    "[pre_match_dctx] cPsi " ^ P.dctxToString cD cPsi ^ 
		    "\n               cPhi " ^ P.dctxToString cD' cPhi_patt ) in 
  begin match (cPsi , cPhi_patt) with
    | (LF.Null     , LF.Null)       -> (matchCands , splitCands)
(*    | (cPsi        , LF.CtxVar _  ) -> ((EqnCtx (cPsi, cPhi_patt) ::  matchCands) , splitCands) *)
    | (cPsi        , LF.CtxVar _  ) -> (matchCands , splitCands)  (* will be unified as part of the contextual obj *)
    | (LF.CtxVar _ , cPhi_patt)     -> (matchCands, SplitCtx (cPsi, cPhi_patt) :: splitCands) 
    | (LF.DDec (cPsi', LF.TypDecl(_, tA)) , LF.DDec (cPhi', LF.TypDecl (_, tB))) -> 
	 let (mC , sC) = pre_match_dctx cOD cOD_p cPsi' cPhi' matchCands splitCands in  
	   pre_match_typ cOD cOD_p (cPsi', (tA, S.LF.id)) (cPhi', (tB, S.LF.id)) mC sC 
    | (_ , _ ) -> raise (MatchError "Ctx mismatch")
  end




(* ********************************************************************************)
(* getSchemaElems : LF.mctx -> LF.dctx -> LF.sch_elem list
 * getSchemaElems cO cPsi
 *    = [F_1, ..., F_n]   if cPsi has a context variable of schema F_1 + ... + F_n
 *    = []                if cPsi has no context variable
 *)
let getSchemaElems cO cPsi =  match Context.ctxVar cPsi with
  | None -> []
  | Some psi ->
      let LF.Schema elems = 
	Store.Cid.Schema.get_schema 
	  (Context.lookupCtxVarSchema cO psi) 
      in
        elems
	  
(* ****************************************************************************** *)
(* Generate object tR of type tP in a context cPsi and meta-context cD            *)

(* genSpine cPsi sA  tP = (cD', tS)

  if {cD} ; cPsi |- sA <= typ   and FMV(sA) = {}
     {cD} ; cPsi |- tP <= typ
  then 
     cD' ; cPsi |- tS : sA <= tP
*)
let rec genSpine cOD cPsi sA tP = begin match Whnf.whnfTyp sA with 
  | (LF.PiTyp ((LF.TypDecl (_, tA) , _ ), tB), s) ->  
      (* cPsi' |- Pi x:A.B <= typ
         cPsi  |- s <= cPsi'
         cPsi  |- tN <= [s]tA
         cPsi |- tN . s <= cPsi', x:A
      *)
(*      let tN         = Whnf.etaExpandMV cPsi (tA,s) idSub in     *)
      let (cO, cD ) = cOD in  
      let tN = etaExpandMVstr cO cPsi (tA,s)  in  
      let _  = dprint (fun () -> "[genSpine] tN = " ^ P.normalToString cD cPsi (tN, S.LF.id) ) in 
      let tS  = genSpine cOD cPsi (tB, LF.Dot(LF.Obj(tN), s))  tP  in 				
	LF.App (tN, tS) 
	
  | (LF.Atom (_ , _a, _tS) as tQ, s) -> 
      (U.unifyTyp LF.Empty cPsi (tQ, s) (tP, idSub);
       LF.Nil )
end 


(* genObj (cD, cPsi, tP) (tH, tA) =  (cD', cPsi', tR, tP')

   if cD ; cPsi |- tH => tA   and 
      there exists a spine tS s.t.  cD ; cPsi |- tS : A > P
   then 
      R = Root (tH, tS) and cD ; cPsi |- tR <= tP   

*)
let rec genObj ((cO, cD), cPsi, tP) (tH, tA) = 
    (* make a fresh copy of tP[cPsi] *)
    let ms    = Ctxsub.mctxToMSub cD in 
    let tP'   = Whnf.cnormTyp (tP, ms) in
    let cPsi' = Whnf.cnormDCtx (cPsi, ms) in 
    let tA'   = Whnf.cnormTyp (Whnf.normTyp (tA, S.LF.id), ms) in 
    let tH'   = Whnf.cnormHead (tH, ms) in 
    let tM = LF.Root (Syntax.Loc.ghost, tH' , genSpine (cO, cD) cPsi' (tA', S.LF.id) tP') in
    let (cD', cPsi', tR, tP', ms') =   
      begin try
	Abstract.abstrCovGoal cPsi'  tM   tP' (Whnf.cnormMSub ms) (* cD0 ; cPsi0 |- tM : tP0 *)
      with Error.Error (_, Error.LeftoverConstraintsAbstract) as e ->
	(print_string ("WARNING: Encountered left-over constraints in higher-order unification\n");
	 print_string ("Coverage goal : " ^ P.normalToString LF.Empty  cPsi' (tM, S.LF.id) ^ " : " ^ 
			  P.typToString LF.Empty cPsi' (tP', S.LF.id) ^ "\n");
	 raise e)
      end
      in 
    let (cPsi', tR', tP')  = (Whnf.normDCtx cPsi', Whnf.norm (tR, S.LF.id), Whnf.normTyp (tP', S.LF.id)) in 
      ((cO,cD') , CovGoal (cPsi', tR', (tP', S.LF.id)), ms')

let rec genAllObj cg tHtA_list = match tHtA_list with 
  | [] -> []
  | tH_tA :: tHAlist -> 
      begin try 
	let cg' = genObj cg tH_tA in 
	   cg' :: genAllObj cg tHAlist 
      with U.Unify _ -> genAllObj cg tHAlist 
      end 

let rec genConst  ((cOD, cPsi, LF.Atom (_, a, _tS)) as cg) = 
  begin
    let _ = Types.freeze a in
    let constructors = (Types.get a).Types.constructors in
      (* Reverse the list so coverage will be checked in the order that the
	 constructors were declared, which is more natural to the user *)
    let constructors = List.rev constructors in   
    let tH_tA_list   = List.map (function c -> (LF.Const c, 
						(Const.get  c).Const.typ)) 
                                constructors 
    in 
      genAllObj cg tH_tA_list
  end 


let rec genHeads (tH, tA) = begin match Whnf.whnfTyp (tA, S.LF.id) with 
  | (LF.Sigma tArec, s) -> 
      let k = LF.blockLength tArec in 
      let rec getComponents i = if i = k+1 then [] 
      else
	(LF.Proj (tH, i) , LF.TClo (LF.getType tH (tArec, s) i 1)) :: getComponents (i+1)
      in 
	getComponents 1
  | _ -> [(tH, tA)]
end 

let rec genBVar ((_cOD, cPsi, _tP) as cg) = 
  let k = Context.dctxLength cPsi in

  let rec genBVarCovGoals i  = if i = (k+1) then []
   else 
    let LF.TypDecl (_ , tA)  = Context.ctxDec cPsi i in   (* x_i : tA   in   cPsi *)
    let tH_tA_list   = genHeads (LF.BVar i , tA) in 
    let cov_goals_i  = genAllObj  cg tH_tA_list in
      cov_goals_i @ genBVarCovGoals (i+1)
  in 
    genBVarCovGoals 1 


let rec genPVar ( (cO,cD), cPsi, tP)   = 
  let _ = dprint (fun () -> "Generate PVar Cases .. \n" ^ P.mctxToString cD ^ " ; " ^ 
		    P.dctxToString cD cPsi ^ "\n      |- " ^ P.typToString cD cPsi (tP, S.LF.id)) in 
  begin
    match Context.ctxVar cPsi with 
    | None -> []
    | Some psi -> 
	let _ = dprint (fun () -> "Generate PVar ") in 
	let cvar_psi = LF.CtxVar psi in
	let selems = getSchemaElems cO cPsi in

	let rec genPVarCovGoals elems = match elems with
	  | [] -> []
	  | LF.SchElem (decls, trec) :: elems -> 
	      let pv_list = genPVarCovGoals elems in 
		
	      let cPhi             = Context.projectCtxIntoDctx decls in
	      let (cD', s, offset) = Ctxsub.ctxToSub_mclosed cD  cvar_psi cPhi in 
		(* cO ; cD' ; psi |- [s]trec  *)
		(* cO ; cD'  |- (cPsi, mshift offset) 
		   cO ; cD' ; (cPsi, mshift offset) |- (tP, mshift offset)
		*)
	      let trec'     = Whnf.normTypRec (trec, s) in 
		
	      let (pdecl, tA)  = (match trec' with LF.SigmaLast tA -> (LF.PDecl (new_parameter_name "p@", tA, cvar_psi) , tA)
				    | LF.SigmaElem _  -> (LF.PDecl (new_parameter_name "p@", LF.Sigma trec', cvar_psi) , LF.Sigma trec')
			   ) in 
		
	      let cD'_pdecl = LF.Dec(cD', pdecl) in
	      let cPsi'  = Whnf.cnormDCtx (cPsi, LF.MShift (offset + 1)) in 
	      let tP'    = Whnf.cnormTyp (tP, LF.MShift (offset + 1)) in 
	      let cg'    = ((cO, cD'_pdecl), cPsi', tP') in 
		
	      let _      = dprint (fun () -> "cg ' = \n  " ^ P.mctxToString cD'_pdecl ^ ";\n  " ^ 
				     P.dctxToString cD'_pdecl cPsi' ^ "\n  |- \n" ^ 
				     P.typToString cD'_pdecl cPsi' (tP', S.LF.id)) in 
	      let id_psi = Substitution.LF.justCtxVar cPsi' in     
		(* cO ; cD_ext, pdec   ; cPsi' |- id_psi : cvar_psi  *)
		
	      let h      = LF.PVar (LF.Offset 1, id_psi) in
	      let tA' = Whnf.normTyp (Whnf.cnormTyp (tA, LF.MShift 1), id_psi) in
		(* cO ; cD', pdec ; cPsi'  |- p[id_psi] : [id_psi](trec[|MShift 1|]) 
		   or to put it differently
		   cO ; cD', pdec ; cPsi'  |- head : trec' 
		*)
	      let tH_tA_list = genHeads (h, tA') in 
	      let cg_list    = genAllObj cg' (tH_tA_list) in
              (* each cg in cg_list:    (cO_k,cD_k), ms_k   
                 where cD_k |- ms_k : cD'_pdcl     
                 we need however:    cD_k |- ms'_k : cD 
                                                  
                    mcomp (MShift (offset + 1) ms_k
               *)
	      let cg_list'    = List.map (fun (cOD',cg, ms) -> (cOD', cg, Whnf.mcomp (LF.MShift (offset + 1)) ms)) cg_list in
		cg_list' @ pv_list 
	in 
	  genPVarCovGoals selems

  end

(* genCovGoals cD cPsi tP = cov_goal list 

   - For each constant for the typeFamily (tP)
      we generate a coverage goal
   
   - For each bound variable in cPsi belonging to the typeFamily(tP),
     we generate a coverage goal

   - For each schema element of a context variable belonging to the typeFamily  (tP),
     we generate a coverage goal.


  A coverage goal is of the following form:

     cD' ; cPsi |- tR : tP  and is represented as  (cD'   ,  CovGoal (cPsi, tR, (tP,s)))

*)

let rec genBCovGoals ((cOD, cPsi, tA) as cov_problem) =  match tA  with
  | LF.Atom _ -> 
      genPVar cov_problem @
      genBVar cov_problem 
  | LF.Sigma trec -> 
      raise (Error "Coverage for parameter variables of sigma type not implemented")
  | LF.PiTyp ((tdecl, dep ) , tA) -> 
      let x = match tdecl with LF.TypDecl (x, _ ) -> x | LF.TypDeclOpt x -> x in 
      let cg_list = genBCovGoals (cOD, LF.DDec (cPsi, tdecl), tA) in 
	List.map (fun (cOD',cg, ms) -> 
		    let CovGoal (LF.DDec(cPsi', tdecl'), tM, sA) = cg in 
		    let cg' = CovGoal (cPsi', LF.Lam (Syntax.Loc.ghost, x, tM), 
				       (LF.PiTyp ((tdecl' , dep), LF.TClo(sA)), S.LF.id)) in 
		      (cOD', cg', ms))
	  cg_list


let rec genCovGoals ((cOD, cPsi, tA) as cov_problem) =  match tA  with
  | LF.Atom _ -> 
     genPVar cov_problem @
      genBVar cov_problem @ genConst cov_problem

  | LF.PiTyp ((tdecl, dep ) , tB) -> 
      let cov_goals = genCovGoals (cOD, LF.DDec (cPsi, tdecl), tB) in 
      let LF.TypDecl (x, _ ) = tdecl in 
	List.map (function (cOD', cg, ms) -> 
		    let CovGoal (LF.DDec (cPsi', tdecl'), tM, sA) = cg in 
		      (cOD', CovGoal (cPsi', LF.Lam (Syntax.Loc.ghost, x, tM), 
				     (LF.PiTyp ((tdecl',dep) , LF.TClo(sA)),
				      S.LF.id)),
		       ms))
	  cov_goals

let rec trivially_empty cov_problem = 
  begin try
    begin match genCovGoals cov_problem with 
      | [] -> true
      | _  -> false
    end
  with Error.Error _ -> (print_endline "Unable to prove remaining open coverage goals trivially empty due to higher-order constraints." ; false)
  end

let rec solve' (cO, cD) (matchCand, ms, cs) cOD_p mCands sCands = match matchCand with 
  | [] -> (match sCands with []  -> Solved
	     | _ -> PossSolvable (Cand (cOD_p , mCands, sCands)))
  | mc :: mCands ->
      begin match mc with
	| Eqn (CovGoal (cPsi, tR, sA) , NeutPatt (cPsi_p, tR_p, sA_p)) -> 
	  let cPsi_p' = Whnf.cnormDCtx (Ctxsub.ctxnorm_dctx (cPsi_p, cs), ms) in 
	  let tR_p'   = Whnf.cnorm (Ctxsub.ctxnorm (tR_p, cs), ms) in 
	  let tA_p'   = Whnf.cnormTyp (Ctxsub.ctxnorm_typ (Whnf.normTyp sA_p, cs), ms) in 
	  let _       = (dprint (fun () -> "[solve] " ^ P.dctxToString cD  cPsi ^ 
				   "    ==    " ^ P.dctxToString cD cPsi_p' );
			 dprint (fun () -> "        " ^ P.typToString cD cPsi sA ^ 
				   "    ==    " ^ P.typToString cD cPsi (tA_p', S.LF.id)) ;
			 dprint (fun () -> "        " ^ 
				   P.normalToString cD cPsi (tR, S.LF.id) ^ 
				   "    ==    " ^ P.normalToString cD cPsi (tR_p', S.LF.id))) in 
	    
	    begin try
	      U.unifyDCtx cD cPsi cPsi_p' ;
	      U.matchTyp cD cPsi sA (tA_p', S.LF.id);
	      U.matchTerm cD cPsi (tR, S.LF.id) (tR_p', S.LF.id) ;
	      solve' (cO,cD) (mCands, ms, cs) cOD_p (mc::mCands) sCands 
	    with
	      (* should this case betaken care of  during pre_match phase ? *)
	      |U.Unify "Context clash" -> 
		 let _ = print_string "Unification of pre-solved equation failed due to context mis-match - initiate context matching" in 
	      	let sc = SplitCtx (cPsi , cPsi_p) in 
		let _ = dprint (fun () -> "Initiate context splitting: " ^ P.dctxToString cD cPsi ^ " == " ^ 
		  P.dctxToString cD cPsi_p' ^ " \n") in 
		  solve' (cO,cD) (mCands, ms, cs) cOD_p mCands (sc::sCands) 
	      | U.Unify msg -> 
	      if U.unresolvedGlobalCnstrs () then 
		let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND") in
		let sc = Split (CovGoal (cPsi, tR, sA) , NeutPatt (cPsi_p, tR_p, sA_p)) in 
		  solve' (cO,cD) (mCands, ms, cs) cOD_p mCands (sc::sCands)
	      else 
		let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ " \n CONSTRAINT NOT SOLVABLE\n") in
		  NotSolvable
	    end

	| EqnCtx (cPsi, cPsi_p) -> 
	    let cPsi_p' = Whnf.cnormDCtx (Ctxsub.ctxnorm_dctx (cPsi_p, cs), ms) in 
	      begin try
		U.unifyDCtx cD cPsi cPsi_p' ;
		solve' (cO,cD) (mCands, ms, cs) cOD_p (mc::mCands) sCands 
	      with U.Unify msg -> 
		  let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ) in
		    NotSolvable
	      end
      end


let rec solve (cO, cD) cOD_p matchCand = match matchCand with 
  | [] -> Solved
  | mc :: mCands ->
  (*  mc =  Eqn (_  , NeutPatt (_, _, _)) ->  *)
      let (cO_p , cD_p) = cOD_p in
      let cs = Ctxsub.cctxToCSub cO_p cD in
      let ms = Ctxsub.mctxToMMSub cD (Ctxsub.ctxnorm_mctx (cD_p,cs)) in 
	solve' (cO,cD) (matchCand ,  ms, cs) cOD_p [] []

(* refineSplits matchL splitL ms = (matchL', splitL')

 if   cD' |- ms : cD 
      cD' |- matchL
      cD  |- splitL 
then 
      cD' |- matchL'    and matchL @ matchL0 = matchL'
      cD' |- splitL'    and splitL' is the refined splitL
*)
let rec refineSplits cOD cOD_p matchL splitL (cs_opt, ms) = match splitL with
  | [] -> (matchL , [] )
  | Split (CovGoal (cPsi, tR, sA) , patt ) :: splits -> 
      (let (matchL', splitL') = refineSplits cOD cOD_p matchL splits (cs_opt, ms) in 
      let tA     = Whnf.normTyp sA in 

      let (cPsi, tR, tA) = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in
      let cPsi  = match cs_opt with None -> cPsi | Some cs -> Ctxsub.ctxnorm_dctx (cPsi, cs) in 
      let tR    = match cs_opt with None -> tR | Some cs -> Ctxsub.ctxnorm (tR, cs) in 
      let tA    = match cs_opt with None -> tA | Some cs -> Ctxsub.ctxnorm_typ (tA, cs) in 

      let (CovGoal (cPsi', tR', sA')  as covG)   = CovGoal (cPsi, tR, (tA, S.LF.id))  in 
      (* let NeutPatt(cPhi, _tN, sB') = patt in *)
      (* let (mL', sL') = pre_match_typ cOD cOD_p (cPsi, sA') (cPhi, sB') matchL' splitL' in   *) 
      (* let (mL', sL') = pre_match_dctx cOD cOD_p cPsi cPhi matchL' splitL' in *)
      let result = pre_match cOD cOD_p covG patt matchL' splitL' in 
	result
      )
  | SplitCtx (cPsi, cPsi_patt ) :: splits -> 
      let (matchL', splitL') = refineSplits cOD cOD_p matchL splits (cs_opt, ms) in 
      let cPsi = Whnf.cnormDCtx (cPsi, ms) in 
      let cPsi'  = match cs_opt with None -> cPsi | Some cs -> Ctxsub.ctxnorm_dctx (cPsi, cs) in 
	pre_match_dctx cOD cOD_p cPsi' cPsi_patt matchL' splitL' 

(* cnormEqn matchL ms = [ms]matchL

   if cD |- matchL 
      cD' |- ms : cD 
  then 
      cD' |- [ms]matchL 
*)
let rec cnormEqn matchL (cs_opt, ms) = begin match matchL with
  | [] -> []
  | (Eqn (CovGoal (cPsi, tR, sA) , patt ) :: matchL') -> 
      let tA     = Whnf.normTyp sA in 

      let (cPsi, tR, tA) = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in 

      let cPsi  = match cs_opt with None -> cPsi | Some cs -> Ctxsub.ctxnorm_dctx (cPsi, cs) in 
      let tR    = match cs_opt with None -> tR | Some cs -> Ctxsub.ctxnorm (tR, cs) in 
      let tA    = match cs_opt with None -> tA | Some cs -> Ctxsub.ctxnorm_typ (tA, cs) in 
      
      let covG0   = CovGoal (cPsi, tR, (tA, S.LF.id)) in 
(*      let cPsi  = match cs_opt with None -> cPsi | Some cs -> Ctxsub.ctxnorm_dctx (cPsi, cs) in 
        let tR    = match cs_opt with None -> tR | Some cs -> Ctxsub.ctxnorm (tR, cs) in 
        let tA    = match cs_opt with None -> tA | Some cs -> Ctxsub.ctxnorm_typ (tA, cs) in 
       let covG0   = CovGoal (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms),
	                      (Whnf.cnormTyp (tA, ms), S.LF.id)) in 
*)
      let matchL0 = cnormEqn matchL' (cs_opt, ms) in 
	Eqn (covG0, patt) :: matchL0
end

(* refine_covprob (cOD_cg, ms) cand = [ms]cand

if (cO,cD) = cOD 
   cD |- ms : cD'
   cO' ; cD' |- cand 
then
   cO ; cD |- [ms]cand

*)

let rec refine_cand (cOD', cs_opt, ms) (cOD, Cand (cOD_p, matchL, splitL)) = 
  let matchL' = cnormEqn matchL (cs_opt, ms) in 
  let (matchL0,splitL0) = refineSplits cOD' cOD_p matchL' splitL (cs_opt, ms) in
    Cand (cOD_p, matchL0, splitL0)

let rec refine_candidates (cOD, cs_opt, ms) ((cO,cD), candidates) = match candidates with
  | [] -> []
  | cand :: cands -> 
      begin try 
	let cand' = refine_cand (cOD,cs_opt, ms) ((cO, cD), cand)  in
	let _ = dprint (fun () -> "REFINED CANDIDATE \n" ^ candToString cOD cand')  in
	  cand' :: refine_candidates (cOD, cs_opt, ms) ((cO,cD), cands)
      with 
	  MatchError _ -> refine_candidates (cOD, cs_opt, ms) ((cO,cD) , cands)
      end


let rec refine_covproblem cov_goals ( ((cO,cD), candidates, (cPhi, tM) ) as cov_problem ) = 
  match cov_goals with 
  | [] -> []
  | (TermCandidate ((cOD_cg', _, ms) as cg)) :: cgs  -> 
       let (cO_cg, cD_cg) = cOD_cg' in 
       let _ = dprint (fun () -> "[Consider coverage goal] \n     " ^ covGoalsToString [cg] ) in 
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^ 
			  " candidates.\n");
		dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms ))   in 

       let candidates' = refine_candidates (cOD_cg', None, ms) ((cO,cD), candidates) in 

       let _ =  dprint (fun () -> "[refine_candidates] DONE : There are
			    remaining #refined candidates = " ^ string_of_int  (List.length candidates')) in 
       let tM'     = Whnf.cnorm (tM, ms) in 
       let cPhi'   = Whnf.cnormDCtx (cPhi, ms) in 
	 (match candidates' with
	   | [] -> (dprint (fun () -> "[OPEN COVERAGE GOAL] " ^ covGoalsToString [cg] ) ; 
	            open_cov_goals := (cOD_cg', cPhi', tM')::!open_cov_goals ; 
		    refine_covproblem cgs cov_problem )
	   | _  -> 
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates') ^ 
			 " refined candidates for " ^ P.normalToString cD_cg cPhi' (tM', S.LF.id) ^ "\n"); 
	       dprint (fun () -> candidatesToString (cOD_cg', candidates', (cPhi', tM'))) ; 
	       ((cOD_cg', candidates', (cPhi', tM')) :: refine_covproblem cgs cov_problem) ) 
	 )
  | CtxCandidate (cOD_cg', cPhi_r, cs, ms) :: cgs  -> 
       let (cO_cg, cD_cg) = cOD_cg' in 
       let _ = dprint (fun () -> "[Consider context goal] \n     " ^ P.dctxToString cD_cg cPhi_r) in 
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^ 
			  " candidates.\n");
		dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms ))   in 

       let candidates' = refine_candidates (cOD_cg', Some cs, ms) ((cO,cD), candidates) in 

       let _ =  dprint (fun () -> "[refine_candidates] DONE : There are
			    remaining #refined candidates = " ^ string_of_int  (List.length candidates')) in 


(*       IMPORTANT: DUE TO HOW cs and ms ARE GENERATED WE MUST FIRST APPLY ms and THEN cs !!
         let tM'     =  Whnf.cnorm (Ctxsub.ctxnorm (tM, cs), ms)  in 
         let cPhi'   = Whnf.cnormDCtx (Ctxsub.ctxnorm_dctx (cPhi,cs), ms) in 
*)
         let tM'     = Ctxsub.ctxnorm (Whnf.cnorm (tM, ms), cs)  in 
         let cPhi'   = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx (cPhi,ms), cs) in 
	 (* cD |- cPhi     and     cD0, cD |- ms : cD ? *)

	 (match candidates' with
	   | [] -> (dprint (fun () -> "[OPEN CONTEXT GOAL] " ^ P.dctxToString cD_cg cPhi_r) ; 
		    dprint (fun () -> "[OPEN COVERAGE GOAL] " ^ P.dctxToString cD_cg cPhi' ^ " . " ^ 
			      P.normalToString cD_cg cPhi' (tM', S.LF.id) );
	            open_cov_goals := (cOD_cg', cPhi', tM')::!open_cov_goals ; 
		    refine_covproblem cgs cov_problem ) 
	   | _  -> 
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates') ^ 
			 " refined candidates for " ^ P.normalToString cD_cg cPhi' (tM', S.LF.id) ^ "\n"); 
	       dprint (fun () -> candidatesToString (cOD_cg', candidates', (cPhi', tM'))) ; 
	       ((cOD_cg', candidates', (cPhi', tM')) :: refine_covproblem cgs cov_problem) ) 
	 )

let rec check_empty_pattern k candidates = match candidates with
  | [] -> []
  | Cand (cOD_p, ml, sl) :: cands -> 
      let sl' = List.filter (fun (Split (CovGoal (_cPsi, tR, _sA) , patt)) -> 
			       match patt with 
				 | EmptyPatt (_cPhi, _sB) -> 
				     (match tR with 
					|LF.Root (_, LF.MVar (LF.Offset k', _ ), LF.Nil ) -> not (k = k' )
					| _ -> true)
				 | _ -> true )
	sl in 
	Cand (cOD_p, ml, sl') :: check_empty_pattern k cands


(* ************************************************************************************* *)

let rec addToCCtx cO cO_tail = match cO_tail with
  | [] -> cO 
  | (LF.CDecl _  as cdec) :: cO_tail -> 
	addToCCtx (LF.Dec(cO, cdec)) cO_tail


(* append (cO, cO_tail) cD1 (cD2 (cpsi, tB)) = (cD1, cD2') 
   
   if  cO, cO_tail |- cD2 mctx
       cO, cO_tail |- cD1 mctx
       cO, cO_tail ; cD1 ; cpsi |- tB 
   then
       cO |- cD1, [psi,x:tB / psi]cD2' mctx
   
*)
let rec append (cO, cO_tail) cD1 (cD2, (cpsi, tB), d) = match cD2 with
  | LF.Empty ->  cD1

  | LF.Dec (cD2', dec) ->
      let cD1' = append (cO, cO_tail) cD1 (cD2', (cpsi, tB), d-1) in
      let k    = List.length cO_tail in 
      let tB'  = Whnf.cnormTyp (tB, LF.MShift (d-1)) in 
      let cs   = LF.CDot (LF.DDec (cpsi, LF.TypDecl (new_bvar_name "@x", tB')), LF.CShift k) in 
      let dec' = match dec with 
	| LF.MDecl(u, tA, cPhi) -> LF.MDecl(u, Ctxsub.ctxnorm_typ (tA, cs), Ctxsub.ctxnorm_dctx (cPhi, cs)) 
	| LF.PDecl(u, tA, cPhi) -> LF.PDecl(u, Ctxsub.ctxnorm_typ (tA, cs), Ctxsub.ctxnorm_dctx (cPhi, cs)) 
      in
        LF.Dec (cD1', dec')


(* cD0, cD |- id(cD) : cD *) 
let rec gen_mid cD0 cD = match cD with 
  | LF.Empty -> LF.MShift (Context.length cD0) 
  | LF.Dec(cD, _mdec) -> 
      let ms' = gen_mid cD0 cD (* cD0, cD |- ms' : cD *)
      in LF.MDot (LF.MV 1, Whnf.mcomp ms' (LF.MShift 1))


(* extend_cs cs (cO, k) = cs' 

   if cO'' |- cs : cO'
     k = |cO|   and cO'' = cO', cO
   then
      cO'' |- cs' : cO', cO  , i.e. cs extended with identity 

*)
let rec extend_cs cs (cO_tail, k) = match (cO_tail, k) with 
  | ([], 0) -> cs
  | (cdec :: cO_tail', k) -> 
      extend_cs (LF.CDot (LF.CtxVar (LF.CtxOffset k), cs)) (cO_tail', (k-1))


(* genCtxGooals (cO, cO_tail) cD (psi:W) = goal_list 

   such that  
   goal-list = 
   [cO, psi:schema, cO_tail ; cD |- psi, x:s_elem_1 , ...
    cO, psi:schema, cO_tail  ; cD |- psi, x:s_elem_n ,
    cO             ; cD |- .  
   ]
*)
let rec genCtxGoals (cO, cO_tail) cD (LF.CDecl (x, sW, dep)) =   
  let LF.Schema elems = Store.Cid.Schema.get_schema sW in 
  let k = List.length cO_tail in 
  let cpsi_offset = LF.CtxOffset (k+1) in   
  let cpsi = LF.CtxVar cpsi_offset in 
  let cO'  = LF.Dec(cO, LF.CDecl(x, sW, dep)) in 
  let cO'' = addToCCtx cO' cO_tail in  

  (* decTomdec cD' cPhi = (cD'' , s) 
    where
    cD'' = cD', cD0   
    cD'' ; cpsi |- s : cPhi
    x:A in cPhi iff x:A[cpsi] in cD0

    and   cO'' |- cD'' mctx 
  *)
  let rec decTomdec cD' decls = match decls with
    | LF.Empty ->   (* (cD', LF.Shift (LF.CtxShift cpsi_offset, 1))  *)
	 (cD', S.LF.id)   
    | LF.Dec(decls, dec) -> 
	let LF.TypDecl (x, tA) = dec in 
        (* . ; decls |- tA : type            *)
        (*  cD' ; cpsi, @x: _  |- s' : decls         *)
	let (cD'', s')  = decTomdec cD'  decls in   
	let (cPsi, (LF.Atom (_ , a, _tS) as tP, s)) = lower cpsi (tA, s') in 
	let (ss', cPsi') = Subord.thin' cO'  a cPsi in  
        (* cPsi |- ss' : cPsi' *)  
        let ssi' = S.LF.invert ss' in
        (* cPsi' |- ssi : cPsi *) 
	let ssi = S.LF.comp s ssi' in 
	let _ = dprint (fun () -> "[genCtx] generated mvar of type " ^ P.dctxToString cD'' cPsi'  ^ " |- " ^ 
			  P.typToString cD'' cPsi' (tP, ssi)) in 
	let mdec = LF.MDecl (x, LF.TClo(tP, ssi), cPsi') in 
	let mv   = LF.Root(Syntax.Loc.ghost, LF.MVar(LF.Offset 1, ss'), LF.Nil) in 
	  (LF.Dec (cD'', mdec) , LF.Dot(LF.Obj mv, s'))
  in 


  (* genCtx elems = ctx_goal_list 

     for each ctx_goal in ctx_goal_list . 
        ctx_goal = (cD_i, cPsi_i, ms_i)  s.t.
        cO ; cD_i |- ms_i   : cD
        cO ; cD_i |- cPsi_i : ctx
  *)
  let rec genCtx  elems  = match elems with 
    | [] -> [] (* [ (cO'', LF.Empty (*? *) , LF.Null, LF.CShift 0, LF.MShift 0) ] *)
    | LF.SchElem (decls, trec) :: elems -> 
	let cPsi_list = genCtx elems in 
	let (cD0, s)   = decTomdec LF.Empty decls in
	let tA = match trec with LF.SigmaLast tA -> LF.TClo (tA, s) | _ -> LF.TClo(LF.Sigma trec, s) in  
	  (* cD0 ; cpsi |- tA : type *)
	let d = Context.length cD in 
	let cD'        = append (cO, cO_tail) cD0 (cD , (cpsi, tA), d) in 
	  (* cO, cO_tail |- cD' mctx and   cD' = cD0, [tB[cpsi]/cpsi] cD *)
	let ms = gen_mid cD0 cD in 
        (* cO, cd, cO_tail ; cD0,cD |- ms : cD 
           cO, cd, cO_tail ; cD' |- cPsi' ctx *)
	let cPsi'      = LF.DDec (cpsi, LF.TypDecl (new_bvar_name "@x" , tA)) in 
	let cPsi''      = Whnf.cnormDCtx (cPsi', LF.MShift (Context.length cD)) in 
	let cs = extend_cs (LF.CDot (cPsi'', LF.CShift (k+1))) (cO_tail, List.length cO_tail) in 
        (* cO, cd, cO_tail |-  CShift (k+1)  : cO
	   cO, cd, cO_tail |- cPsi', CShift (k+1) : cO, cd
       	   cO, cd, cO_tail |- id(cO_tail), cPsi', CShift (k+1) : cO, cd, cO_tail
        *)
	let _ = dprint (fun () -> "[genCtx] " ^  P.dctxToString cD' cPsi'' ^ "\n") in 
	let _ = dprint (fun () -> "ms = " ^ P.msubToString cD' ms ^ "\n") in 
	   (cO'', cD' , cPsi'', cs , ms) :: cPsi_list 
  in  
   genCtx elems  

(* Find mvar to split on *)

let rec addToMCtx ((cO, cD) as cOD') (cD_tail, ms) = match cD_tail with
  | [] -> (cOD' , ms)
  | LF.MDecl (u, tA, cPsi) :: cD_tail -> 
      let mdec = LF.MDecl(u, Whnf.cnormTyp (tA, ms), Whnf.cnormDCtx (cPsi, ms)) in 
	addToMCtx (cO, LF.Dec (cD, mdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.PDecl (u, tA, cPsi) :: cD_tail -> 
      let pdec = LF.PDecl(u, Whnf.cnormTyp (tA, ms), Whnf.cnormDCtx (cPsi, ms)) in 
	addToMCtx (cO, LF.Dec (cD, pdec)) (cD_tail, Whnf.mvar_dot1 ms)


(* let rec mdot  ms k = match k with
  | 0 -> ms
  | k -> mdot (Whnf.mvar_dot1 ms) (k-1)
*)

let genCGoals ((cO, cD') as cOD) mdec = match mdec with
  | LF.MDecl (_u, tA, cPsi) -> 
      let _ = dprint (fun () -> "[SPLIT] CovGoal : " ^ P.dctxToString cD' cPsi ^ " . " ^ 
			P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in 
      let dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
	(genCovGoals (cOD, cPsi, Whnf.normTyp (tA, S.LF.id)) , dep0) 
  | LF.PDecl (_u, tA, cPsi) -> 
      let _ = dprint (fun () -> "[SPLIT] CovGoal (PVAR): " ^ P.dctxToString cD' cPsi ^ " . " ^ 
			P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in 
      let _ dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
      (* bp : This may potentially even loop! ; 
	 but this could initiate a potential split of PV including splitting the context 
	 g |- #A  chould result in  g',x|- x   g',x|- #q 
         in this implementation, we assume that the context split has been done separetely,
	 and hence we would only loop if we were to split #p (and initiate another context split)
      *)
	(* (genBCovGoals (cOD, cPsi, tA), dep0) *)
	raise (Error "PVAR CASE NOT IMPLEMENTED") 


let rec best_ctx_cand (cO, cv_list) cD k cO_tail = match (cv_list , cO) with 
  | ([] , _ )  -> NoCandidate
  | [LF.CtxOffset j] , LF.Dec (cO', cd)  -> 
      if k = j then 
	let ctx_goals = genCtxGoals (cO', cO_tail) cD cd in  
	let ctx_goals' = List.map (fun (cO', cD', cPhi, cs, ms) -> 
				       (* cO' |- cs : cO 
                                          cO'; [cs]cD' |- ms : [cs]cD
				       *)
				     let _ = dprint (fun () -> "[ctx_goal] = " ^ 
						       P.mctxToString cD' ^ " \n " ^ 
						       P.msubToString cD' ms ^ "\n" ^ 
						       P.dctxToString cD' cPhi ^ "\n") in 
					 CtxCandidate ((cO', cD') , cPhi,  cs, ms )
                                    ) 
                            ctx_goals in 
            SomeCtxCands ctx_goals' 
      else
	best_ctx_cand (cO', cv_list) cD (k+1) (cd::cO_tail)



let rec best_cand (cO,cv_list) (cD, mv_list) k cD_tail  = 
match (mv_list, cD) with 
  | ([] , _ )  -> NoCandidate
  | (LF.Offset j :: mvlist' ,  LF.Dec (cD', md))->        
      if k = j then 
	begin try
	  let (cov_goals' , dep0) =  genCGoals (cO,cD') md  in
	  let cov_goals0 = List.map (fun (cOD', cg, ms) -> 
				       let CovGoal (cPsi', tR, sA') = cg in 
				       let ms' = LF.MDot (LF.MObj ( Context.dctxToHat cPsi' , tR),  ms) in  
				       let k = List.length cD_tail in 
				       let (cOD'', ms0) = addToMCtx cOD' (cD_tail, ms') in 
				       let cg' = CovGoal (Whnf.cnormDCtx (cPsi', LF.MShift k) , 
							  Whnf.cnorm (tR, LF.MShift k) ,
							  (Whnf.cnormTyp (Whnf.normTyp sA' , LF.MShift k), S.LF.id)) in 
					 TermCandidate (cOD'' , cg',  ms0 )				   
				    )
                           cov_goals'
	  in 
	    
	    match best_cand (cO, cv_list) (cD', mvlist') (k+1) (md::cD_tail) with 
	      | NoCandidate -> SomeTermCands (dep0, cov_goals0)
	      | SomeTermCands (dep, cov_goals) -> 
		  (match (dep, dep0) with 
		     | (Dependent,  Atomic) -> SomeTermCands (dep, cov_goals)
		     | (Atomic,  Dependent) -> SomeTermCands (dep0, cov_goals0)
		     | ( _       , _      ) -> (if  List.length cov_goals < List.length cov_goals0 
						then SomeTermCands (dep, cov_goals) else SomeTermCands (dep0, cov_goals0 )
					       )	
		  )
	  with Error.Error (_, Error.LeftoverConstraintsAbstract) ->
	    (print_endline ("WARNING: Encountered left-over constraints in higher-order unification.\n\
                             Try another candidate.");
	     best_cand (cO,cv_list) (cD', mvlist') (k+1) (md::cD_tail))
	end
      else 
	best_cand (cO, cv_list) (cD', mv_list) (k+1) (md::cD_tail)



(* best_candidate cO cD = cov_goals

   cov_goals is a list of coverage goals   CovGoal (cOD', cg, ms) 

   where

   cg = CovGoal (cPsi, tR, sA) and   cOD' |- ms : cO;cD 

*)

let rec mvInSplitCand cOD vlist candidates = match candidates with
  | [] -> vlist
  | Cand(_, _ , sl) :: cands -> 
      mvInSplitCand cOD (mvInSplit cOD vlist sl) cands
      
and mvInSplit cOD vlist slist = match slist with
  | [] -> vlist
  | Split (CovGoal (_, LF.Root (_ , LF.MVar (u, _ ) , _ ), _ ), _ ) :: sl -> 
      let (cvlist , mvlist) = vlist in 
      if List.mem u mvlist then 
	mvInSplit cOD vlist sl 
      else mvInSplit cOD (cvlist, (u::mvlist)) sl

  | Split (CovGoal (_, LF.Root (_ , LF.PVar (p, _ ) , _ ), _ ), _ ) :: sl -> 
      let (cvlist , mvlist) = vlist in 
      if List.mem p mvlist then 
	mvInSplit cOD vlist sl 
      else mvInSplit cOD (cvlist, (p::mvlist)) sl

  | Split (CovGoal (_, LF.Root (_ , LF.Proj (_ , _ ), _tS), _tA) as cg , patt)  :: sl -> 
      let (_, cD) = cOD in 
      dprint (fun () -> "SPLIT CAND (SIGMA) : " ^ covGoalToString cOD cg ^ " == " ^ 
		 pattToString cD patt ) ; 
      mvInSplit cOD vlist sl 

  | SplitCtx (LF.CtxVar psi, cPhi) :: sl -> 
      let (cvlist , mvlist) = vlist in 
(*	mvInSplit cOD (psi::cvlist, mvlist) sl  *)
	if List.mem psi cvlist then 
	mvInSplit cOD (cvlist, mvlist) sl 
      else mvInSplit cOD (psi::cvlist, mvlist) sl




let rec best_split_candidate cO cD candidates = 
  (* assume candidates are non-empty *)
  let (cvsplit_list, mvsplit_list)  = mvInSplitCand (cO, cD) ([], []) candidates in 
  let mv_list_sorted = List.sort (fun (LF.Offset k) -> fun (LF.Offset k') -> if k' < k then 1 else (if k' = k then 0 else -1)) 
                                 mvsplit_list in 
  let cv_list_sorted = List.sort (fun (LF.CtxOffset k) -> fun (LF.CtxOffset k') -> if k' < k then 1 else (if k' = k then 0 else -1)) 
                                 cvsplit_list in 

  let _ = dprint (fun () -> "SHOW SPLIT CANIDATE LIST " ^ mvlistToString mv_list_sorted ) in  
   if cv_list_sorted = [] then    
     best_cand (cO, cv_list_sorted)  (cD, mv_list_sorted) 1 [] 
   else
     (dprint (fun () -> "Context Split possible\n") ;
      best_ctx_cand (cO, cv_list_sorted) cD 1 [] )


(* ************************************************************************************* *)

let rec refine ( ((cO,cD), candidates, (cPhi,tM)) as cov_problem )  = 
  begin match cD with
    | LF.Empty  -> 
	((* print_string (candidatesToString cov_problem ) ; *)
	 open_cov_goals := ((cO,cD), cPhi, tM)::!open_cov_goals ; 
	 raise NothingToRefine
	 (* [] *))
	(* raise (Error "Nothing to refine"))*)
    | _  -> 
	let cov_goals' = best_split_candidate cO cD candidates in 
	let _ = dprint (fun () -> "[Original candidates] \n" ^ candidatesToString cov_problem ) in
	  begin match (cov_goals', candidates ) with
	    | (SomeCtxCands ctx_goals, [] )  ->  []
	    | (SomeCtxCands ctx_goals,  _ )  -> (* bp : TODO refine_ctx_covproblem ctx_goals cov_problem *)
(*		 raise (Error "Context refinmenet not implemented yet") *)
  		  refine_covproblem ctx_goals cov_problem	
	    | (SomeTermCands (_, []), [])  -> [] 
	    | (SomeTermCands (_, []), _ )  -> [((cO,cD), check_empty_pattern 1 candidates, (cPhi, tM ) )]
	    | (SomeTermCands (_, cgoals), _ )  -> 
		let _ = dprint (fun () -> 
				  let cgs = List.map (fun (TermCandidate cg) -> cg) cgoals in 
				    "[Generated coverage goals] \n     " ^ covGoalsToString cgs ) in 
  		  refine_covproblem cgoals cov_problem	
	    | (NoCandidate,   [] ) -> []
	    | (NoCandidate, _    ) -> 
		raise (Error "No coverage goals generated")
	  end 
  end 
	
let rec check_all f l = (match l with
  | [] -> ()
  | h::t -> 
      ((try f h with MatchError _  -> dprint (fun () ->  "MATCH ERROR"  )
                   | NothingToRefine  -> dprint (fun () ->  "Nothing to refine ERROR" )); (* ??? *)
       check_all f t )
			)
(* At least one of the candidates in cand_list must be solvable,
   i.e. splitCand = []  and matchCand are solvable  
*)

	    

let rec check_covproblem cov_problem = 
  let ( (cO , cD ) , candidates, cg) = cov_problem in 
  let rec existsCandidate candidates nCands open_cg =  match candidates with
    | [] -> 
	let cov_prob' = ( (cO, cD ), nCands, cg)  in 
	  (* there were candidates – refine coverage problem *)
	  open_cov_goals := open_cg @ !open_cov_goals;
	  check_coverage (refine cov_prob')
    | ((Cand (cOD_p, matchCand, splitCand )) as c) :: cands ->  
	(match splitCand with 
	   |  [] -> 
		let ( (cO , cD ) , _candidates, (cPhi, tM)) = cov_problem in 
		let _ = dprint (fun () -> "Check whether " ^ P.dctxToString  cD  cPhi ^ " |- " 
				  ^ P.normalToString cD cPhi (tM, S.LF.id) ^
				  " is covered?\n") in 
		(match solve (cO, cD) cOD_p matchCand with 
		   | Solved -> (* No new splitting candidates and all match
				  candidates are satisfied *) 
	       let ( (cO , cD ) , _ , (cPhi, tM)) = cov_problem in 
		 dprint (fun () -> "[check_covproblem] COVERED " ^ P.dctxToString cD
			   cPhi ^ " |- " ^ P.normalToString cD cPhi (tM, S.LF.id)) ; 
		       (* Coverage succeeds *)   ()
		   | PossSolvable cand -> 
		       (* Some equations in matchCand cannot be solved by hounif;
			  they will be resurrected as new splitting candidates *)
		       existsCandidate cands (cand :: nCands) open_cg
		   | NotSolvable -> (* match candidates were not solvable; this candidate gives rise to coverage failure ? *)
		       let ( (cO , cD ) , _candidates, (cPhi, tM)) = cov_problem in 
		       let open_goal = ((cO, cD), cPhi,  tM) in 
	               (* open_cov_goals := ((cO, cD), cPhi,  tM)::!open_cov_goals ;  *)
		       existsCandidate cands nCands  (open_goal::open_cg)
		) 
	   | _ ->  existsCandidate cands  (c :: nCands)  open_cg
	)
  in 
    existsCandidate candidates [] []

(*  let rec existsCandidate candidates nCands =  match candidates with
    | [] -> 
	let cov_prob' = ( (cO, cD ), nCands, cg)  in 
	  (* there were candidates – refine coverage problem *)
	  check_coverage (refine cov_prob')
    | ((Cand (cOD_p, matchCand, splitCand )) as c) :: cands ->  
	(match splitCand with 
	   |  [] -> 
		(match solve (cO, cD) cOD_p matchCand with 
		   | Solved -> (* No new splitting candidates and all match candidates are satisfied *) 
		       (* Coverage succeeds *)   ()
		   | PossSolvable cand -> 
		       (* Some equations in matchCand cannot be solved by hounif;
			  they will be resurrected as new splitting candidates *)
		       existsCandidate cands (cand :: nCands)
		   | NotSolvable -> (* match candidates were not solvable; this candidate gives rise to coverage failure ? *)
		       let ( (cO , cD ) , candidates, (cPhi, tM)) = cov_problem in 
	               open_cov_goals := ((cO, cD), cPhi, tM)::!open_cov_goals ; 
		       existsCandidate cands nCands
		) 
	   | _ ->  existsCandidate cands  (c :: nCands) 
	)
  in 
    existsCandidate candidates []
*)
and check_coverage cov_problem_list = 

  check_all (function  cov_prob -> check_covproblem cov_prob )   cov_problem_list


(* ****************************************************************************** *)

(* Flags *)
let enableCoverage = ref false  (* true iff coverage should be checked *)
let warningOnly    = ref false     (* true iff failed coverage should generate a warning *)
let no_covers = ref 0           (* number of times coverage checking has yielded a negative result *)

(* ****************************************************************************** *)
(* Printing for debugging *)
(* 
 * Print the list of constructors and types (just for debugging)
 *)
let rec dprintCTs cO cD cPsi = function
        | [] -> dprnt ""
        | (c, cSig) :: rest ->
             (dprnt ("\"" ^ R.render_name (Const.get c).Const.name ^ "\""
                   ^ " : " ^ P.typToString cD cPsi (cSig, idSub));
              dprintCTs cO cD cPsi rest)


let rec extract_patterns tA branch_patt = match branch_patt with 
  | BranchBox (cO, cD, (cPsi, NormalPattern (tR, _ ), ms, cs)) -> 
      ( (cO, cD),  NeutPatt (cPsi, tR, (Whnf.cnormTyp (Ctxsub.ctxnorm_typ (tA, cs) ,ms), S.LF.id)) )
  | BranchBox (cO, cD, (cPsi, EmptyPattern, ms, cs)) -> 
      ( (cO, cD), EmptyPatt (cPsi, (Whnf.cnormTyp (Ctxsub.ctxnorm_typ (tA, cs),ms), S.LF.id)) )


(* initialize_coverage problem = 
      
*)
let rec initialize_coverage problem = 

  let (tA, cPsi) = problem.ctype in 
  let cO'        = problem.cO in 
  let cD'        = LF.Dec (problem.cD, LF.MDecl(Id.mk_name (Id.NoName), tA, cPsi)) in   
  let mv         = LF.MVar (LF.Offset 1, idSub) in 
  let tM         = LF.Root (Syntax.Loc.ghost, mv, LF.Nil) in 
  let cPsi'      = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
  let sA'        = (Whnf.cnormTyp (tA, LF.MShift 1), S.LF.id) in 
  let covGoal    = CovGoal (cPsi', tM, sA') in 

  let pat_list  = List.map (function b -> extract_patterns tA b) problem.branches in 

  let rec gen_candidates covGoal patList = match patList with 
    | [] -> [] 
    | (cOD, EmptyPatt (cPsi, sA) ) :: plist -> 
	if trivially_empty (cOD, cPsi, Whnf.normTyp sA) then 
	  gen_candidates covGoal plist 
	else 
	  raise (NoCover (fun () -> let (cO, cD) = cOD in 
			    Printf.sprintf "\n##   Empty Pattern ##\n   %s\n\n##   Case expression of type : \n##   %s\n##   is not empty.\n\n" 
			      (Pretty.string_of_loc problem.loc)
			      (P.typToString cD cPsi sA)))
(*	  raise (Error "COVERAGE CANNOT PROVE A TYPE TRIVIALLY EMPTY")*)
    | ((cO, cD) as cOD, (NeutPatt(cPhi, _tN, sB') as pat)) :: plist -> 
	let _ = dprint (fun () -> "PATTERN : \n     " ^ P.mctxToString cD ^ " |- " ^  pattToString cD pat)  in 

	let ml0, sl0   = pre_match_dctx (cO', cD') cOD cPsi' cPhi [] [] in 
	let (ml', sl') = pre_match_typ (cO',cD') cOD (cPsi', sA') (cPhi, sB') ml0 sl0 in  
	let (ml, sl)   = pre_match (cO',cD') cOD covGoal pat ml' sl' in 
	  Cand (cOD, ml, sl) :: gen_candidates covGoal plist 
  in 
  let cand_list =  gen_candidates covGoal pat_list in 

    [ ( (cO',cD') , cand_list , (cPsi', tM) ) ] 

let rec check_emptiness cO cD = match cD with
  | LF.Empty -> false
  | LF.Dec(cD', LF.MDecl (_u, tA, cPsi)) -> 
      begin try
	(match genCovGoals ((cO, cD') , cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> true
	   | _  -> check_emptiness cO cD'
	) 
      with Error.Error (_, msg) ->
	print_string ("Unable to prove : " ^ P.typToString cD' cPsi (tA, S.LF.id) ^ " to be empty \n") ;
	print_string "Try next meta-variable ...\n"; 
	check_emptiness cO cD'
      end 
  | LF.Dec(cD', LF.PDecl (_u, LF.Sigma _ , _cPsi)) -> 
      check_emptiness cO cD'
  | LF.Dec(cD', LF.PDecl (_u, tA, cPsi)) -> 
      begin try
	(match genBCovGoals ((cO, cD') , cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> true
	   | _  -> check_emptiness cO cD'
	) 
      with Error.Error (_, msg) ->
	print_string "Unable to prove given type is empty\n" ; check_emptiness cO cD'
      end 

let rec revisit_opengoals ogoals = begin match ogoals with
  | [] -> ([], [])
  | (((cO, cD), _cPsi, _tM) as og) :: ogoals -> 
      if check_emptiness cO cD then 
        let (oglist , trivial_list) = revisit_opengoals ogoals in 
	  (oglist, og::trivial_list)
      else 
	let (oglist, trivial_list) = revisit_opengoals ogoals in 
	  (og :: oglist, trivial_list)
end 

let check_coverage_success problem  =  
(Debug.popIndentationLevel() ;        
 begin match problem.prag with
   | Pragma.RegularCase -> 
       if !open_cov_goals = [] then 
	 (dprint (fun () -> "## COVERS ##");
	  Success)
       else 
	 (* Check if the open coverage goals can be proven to be impossible *)
         Failure (fun () ->
                   Printf.sprintf "\n##   Case expression doesn't cover: ##\n##   %s\n##   %s\n\n"
                     (Pretty.string_of_loc problem.loc)
                     ("CASE(S) NOT COVERED :\n" ^ opengoalsToString (!open_cov_goals) ))

   | Pragma.PragmaNotCase ->
       if !open_cov_goals = [] then 
	 Failure (fun () ->
                    Printf.sprintf "\n##   Case expression covers : ##\n##   %s\n##\n\n"
                      (Pretty.string_of_loc problem.loc))
       else 
	 ( (Printf.printf "\n##   Case expression doesn't cover, consistent with \"case ... of %%not\" ##\n##   %s\n##   %s\n\n"
            (Pretty.string_of_loc problem.loc)
            ("CASE(S) NOT COVERED :\n" ^ opengoalsToString (!open_cov_goals) )) ; 
	  Success )
 end 
)



(* covers problem = ()

  problem  = {loc: loc ; prag : pragma ; 
              cO : LF.mctx ; cD : LF.mctx ;
              branches ; ctype : tA[cPsi] }

  where   cO ; cD ; cPsi |- tA  

  Succeeds, if there is at least one pattern which covers elements of type tA[Psi] 
  Fails, otherwise
*)
let covers problem =
if not (!enableCoverage) 
  then Success
else
  (let (tA, cPsi) = problem.ctype in
  let _ = (dprint (fun () -> "[covers] cPsi = " ^ 
		     P.dctxToString problem.cD cPsi);
	   dprint (fun () -> "           tA = " ^ 
		     P.typToString problem.cD cPsi (tA,idSub) )) in   
  let _ = (Debug.pushIndentationLevel(); Debug.indent 2) in 
  let _ = U.resetGlobalCnstrs () in 

  let cov_problems = initialize_coverage problem in 

    dprint (fun () -> "Coverage checking a case with "
              ^ string_of_int (List.length problem.branches)  
	      ^ " branch(es) at:\n"
              ^ Pretty.string_of_loc problem.loc);

    dprint (fun () -> "Initial coverage problem \n" ^ covproblemsToString cov_problems ) ; 
    
    check_coverage cov_problems ;  (* there exist all cov_problems are solved *) 
    let o_cg         = !open_cov_goals in 
    let r            = List.length  o_cg in 
    let (revisited_og, trivial_og) = revisit_opengoals o_cg in 
    let r'           = List.length (revisited_og) in 

    if r  > r' then 
      (print_endline "\n(Some) coverage goals were trivially proven to be impossible.";
       print_endline ("CASES TRIVIALLY COVERED in line " ^
			 Pretty.string_of_loc  problem.loc
		      ^ " : " ^ string_of_int (List.length (trivial_og)))
(* opengoalsToString trivial_og *)
)
    else () ; 

    open_cov_goals :=  revisited_og ; 
    check_coverage_success problem
  )

let process problem =
  reset_cov_problem () ; 
  match covers problem with
  | Success -> ()
  | Failure messageFn ->
      if !warningOnly then
        Error.addInformation ("WARNING: Cases didn't cover: "  ^ messageFn()) 
      else
        raise (NoCover messageFn)



let problems = ref ([] : problem list)

let clear () =
  problems := []

let stage problem =
  problems := problem::!problems

let force f =
  List.map (fun problem -> f (covers problem)) (List.rev !problems)

