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
module R = Store.Cid.NamedRenderer

let idSub  = S.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)
let idMSub = Whnf.m_id

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [29])

type error =
    NoCover of string
  | MatchError of string
  | NothingToRefine
  | NoCoverageGoalsGenerated

exception Error of Syntax.Loc.t * error

let _ = Error.register_printer
  (fun (Error (loc, e)) ->
    Error.print_with_location loc (fun ppf ->
      match e with
	| NoCover s -> Format.fprintf ppf "Coverage checking failed: %s" s
	| MatchError s -> Format.pp_print_string ppf s
	| NothingToRefine -> Format.pp_print_string ppf "Nothing to refine"
	| NoCoverageGoalsGenerated -> Format.pp_print_string ppf "No coverage goals generated"))

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

type problem = {loc : Syntax.Loc.t;
                prag : Pragma.case_pragma;           (* indicates if %not appeared after ``case...of'' *)
                cD : LF.mctx;
                branches : Comp.branch list;
                ctype : (LF.typ * LF.dctx)}         (* type and context of scrutinee *)

(* Make a coverage problem *)
let make loc prag cD branches cA =
  {loc= loc;
   prag= prag;
   cD= cD;
   branches= branches;
   ctype = cA}

(* Final Coverage Result *)
type coverage_result =
  | Success
  | Failure of string

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
    Cand of  LF.mctx *                  (* meta-context of pattern                 *) 
              eqn list * split list 

type candidates = candidate list

let open_cov_goals  = ref ([]   :  (LF.mctx * LF.dctx * LF.normal) list )

let reset_cov_problem () = open_cov_goals := [] 

type solved = Solved | NotSolvable | PossSolvable of candidate

type refinement_candidate = 
  | TermCandidate of (LF.mctx * cov_goal * LF.msub)  
  | CtxCandidate of (LF.mctx * LF.dctx * LF.msub) 

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


let rec etaExpandMVstr cD cPsi sA  = etaExpandMVstr' cD cPsi (Whnf.whnfTyp sA)  

and etaExpandMVstr' cD cPsi sA  = match sA with
  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cPsi in  
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let tQ    = ConvSigma.strans_typ (tP, s) conv_list in
      (*  cPsi |- s_proj : cPhi
          cPhi |- tQ   where  cPsi |- tP   and [s_proj]^-1([s]tP) = tQ  *)

      let (ss', cPhi') = Subord.thin' cD a cPhi in  
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
      LF.Lam (Syntax.Loc.ghost, x, etaExpandMVstr cD (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s) )

    

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


let rec covGoalToString cD cg = 
  let CovGoal(cPsi, tR, sA) = cg in 
    P.dctxToString cD cPsi ^ " . " ^ 
    P.normalToString cD cPsi (tR, S.LF.id) ^ " : " ^ P.typToString cD cPsi sA 

let rec covGoalsToString cov_goals = match cov_goals with 
  | [] -> "\n"
  | (cD, cg, _ ) :: cgoals -> 
      covGoalToString cD cg ^ "\n     " ^  covGoalsToString  cgoals 

let rec splitsToString cD cD_p splits = match splits with 
  | [] -> "\n"
  | (Split (cg, patt) :: splits ) ->       
      covGoalToString cD cg ^ " == " ^ pattToString cD_p patt ^ "\n   " 
      ^ splitsToString cD cD_p splits
  | (SplitCtx (cPsi, cPhi) :: splits ) -> 
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    " 
      ^  splitsToString cD cD_p splits

let rec eqnsToString cD cD_p eqns = match eqns with 
  | [] -> "\n"
  | (Eqn (cg, patt) :: eqns ) -> 
      covGoalToString cD cg ^ " == " ^ pattToString cD_p patt ^ "\n   " 
      ^ eqnsToString cD cD_p eqns
  | (EqnCtx (cPsi, cPhi) :: splits ) -> 
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    " 
      ^  eqnsToString cD cD_p splits


let rec candToString cD (Cand (cD_p, eqns, splits)) = 
	 P.mctxToString cD     ^ " ; \n"  ^
	 P.mctxToString cD_p ^ " \n   |- \n" ^ 
	 " MATCHES { \n    " ^ eqnsToString cD (cD_p) eqns ^ "         }\n" ^ 
	 " SPLITS { \n    " ^ splitsToString cD (cD_p) splits ^ "          }\n]\n" 


let rec candidatesToString' cD candidates k = match candidates with  
  | [] -> "\n\n"
  | (Cand (cD_p, eqns, splits) :: cands) -> 
       "[CANDIDATE " ^ string_of_int k ^ " : \n" ^ 
	 P.mctxToString cD     ^ " ; \n"  ^
	 P.mctxToString cD_p ^ " \n   |- \n" ^ 
	 " MATCHES { \n    " ^ eqnsToString cD cD_p eqns ^ "         }\n" ^ 
	 " SPLITS { \n    " ^ splitsToString cD cD_p splits ^ "          }\n]\n" ^ 
	 candidatesToString' cD  cands (k+1)

let candidatesToString (cD, candidates, (cPsi,tM) ) = 
"COVERAGE GOAL : " ^ 
P.mctxToString cD ^ " ; " ^ P.dctxToString cD cPsi ^ "\n   |-  \n" ^ 
P.normalToString cD cPsi (tM, S.LF.id) ^ "\nCOVERED BY\n" ^ 
candidatesToString' cD candidates 1

let rec covproblemsToString cov_problems = match cov_problems with
  | [] -> "\n"
  | cov_prob :: cov_probs -> 
      candidatesToString cov_prob ^ "\n   " ^ covproblemsToString cov_probs


let rec goalsToString ogoals k = match ogoals with 
  | [] -> ""
  | (cD, cPsi, tM) :: ogoals -> 
      "\n(" ^ string_of_int k ^ ")   " ^ 
        P.mctxToString cD ^ "\n " ^ 
	P.dctxToString cD cPsi ^ "\n   |-  " ^
	P.normalToString cD cPsi (tM, S.LF.id) ^ "\n" ^ 
	goalsToString ogoals (k+1) 


let rec opengoalsToString ogoals = goalsToString ogoals 1


(* ****************************************************************************** *)

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
let rec pre_match cD cD_p covGoal patt matchCands splitCands = 

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

	  pre_match cD cD_p covGoal' patt' matchCands splitCands

    | (LF.Root (_ , tH, tS), LF.Root (_, tH', tS')) -> 
	begin match pre_match_head (cPsi, tH) (cPhi, tH') with 
	  | Yes (sA, sA') -> 	  
	      pre_match_spine  cD cD_p 
		               (cPsi , tS , sA)  
		               (cPhi , tS', sA')
		               matchCands splitCands
	  | No            -> raise (Error (Syntax.Loc.ghost, MatchError "Head mismatch"))
	  | Inst          -> 
	      (Eqn (covGoal, patt) :: matchCands , splitCands)
	  | SplitCand     -> (matchCands , Split (covGoal, patt)::splitCands)
	end
  end

and pre_match_spine cD cD_p (cPsi , tS , sA)
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

	let (matchCands', splitCands') = pre_match cD cD_p covGoal1 patt1 matchCands splitCands in 

	  pre_match_spine cD cD_p (cPsi , tS , sB2')
                                    (cPsi', tS', sC2') matchCands' splitCands'
  end

let rec pre_match_typ cD cD_p (cPsi, sA) (cPhi, sB) matchCands splitCands = 
  let _ = dprint (fun () -> 
		    let cD' = cD_p in 
		      "[pre_match_typ] sA = " ^ P.typToString cD cPsi sA ^ "\n" ^ 
		      "                sB = " ^ P.typToString cD' cPhi sB) in 
    match (Whnf.whnfTyp sA , Whnf.whnfTyp sB) with 
  | (LF.Atom (_, a, tS1) , s1) , (LF.Atom (_, b, tS2), s2) -> 
      let tK1 = (Types.get a).Types.kind in
      let tK2 = (Types.get b).Types.kind in
      let tS1' = Whnf.normSpine (tS1, s1) in 
      let tS2' = Whnf.normSpine (tS2, s2) in 
	if a = b then 
	  pre_match_typ_spine cD cD_p (cPsi, tS1', (tK1, S.LF.id)) (cPhi, tS2', (tK2, S.LF.id))
                              matchCands splitCands
	else raise (Error (Syntax.Loc.ghost, MatchError "Type Head mismatch"))
  | (LF.PiTyp ((LF.TypDecl(x, tA1), _ ), tA2), s1) ,  (LF.PiTyp ((LF.TypDecl(y, tB1), _ ), tB2), s2) -> 
      let (matchCands' , splitCands') = pre_match_typ cD cD_p (cPsi, (tA1, s1)) (cPhi, (tB1, s2)) 
	                                              matchCands splitCands
      in 
	pre_match_typ cD cD_p (LF.DDec (cPsi, LF.TypDecl (x, LF.TClo (tA1, s1))), (tA2, S.LF.dot1 s1))
                                (LF.DDec (cPhi, LF.TypDecl (y, LF.TClo (tB1, s1))), (tB2, S.LF.dot1 s2))
         	      matchCands' splitCands'

  | (LF.Sigma trec1 , s1) , (LF.Sigma trec2, s2) -> 
      pre_match_trec cD cD_p cPsi cPhi (trec1, s1) (trec2, s2) 
	matchCands splitCands

      

and pre_match_trec cD cD_p cPsi cPhi srec1 srec2 matchCands splitCands = match (srec1, srec2) with
  | (LF.SigmaLast tA1, s1)  , (LF.SigmaLast tA2, s2) -> 
      pre_match_typ cD cD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands
  | (LF.SigmaElem (x1, tA1, trec1) , s1) , (LF.SigmaElem (x2, tA2, trec2) , s2) -> 
      let (mC, sC) = pre_match_typ cD cD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands in 
	pre_match_trec cD cD_p (LF.DDec(cPsi, LF.TypDecl(x1, LF.TClo(tA1,s1)))) (LF.DDec(cPhi, LF.TypDecl(x2, LF.TClo(tA2,s2))))
	  (trec1, S.LF.dot1 s1) (trec2, S.LF.dot1 s2) 
	  mC sC

and pre_match_typ_spine cD cD_p (cPsi, tS1, sK1) (cPsi', tS2, sK2) 
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

	let (matchCands', splitCands') = pre_match cD cD_p covGoal1 patt1 matchCands splitCands in 

	  pre_match_typ_spine cD cD_p (cPsi , tS , sK1')
                                        (cPsi', tS', sK2') matchCands' splitCands'
  end
 


let rec pre_match_dctx cD cD_p cPsi cPhi_patt matchCands splitCands = 
  let _ = dprint (fun () -> 
		  let cD' = cD_p in 
		    "[pre_match_dctx] cPsi " ^ P.dctxToString cD cPsi ^ 
		    "\n               cPhi " ^ P.dctxToString cD' cPhi_patt ) in 
  begin match (cPsi , cPhi_patt) with
    | (LF.Null     , LF.Null)       -> (matchCands , splitCands)
(*    | (cPsi        , LF.CtxVar _  ) -> ((EqnCtx (cPsi, cPhi_patt) ::  matchCands) , splitCands) *)
    | (cPsi        , LF.CtxVar _  ) -> (matchCands , splitCands)  (* will be unified as part of the contextual obj *)
    | (LF.CtxVar _ , cPhi_patt)     -> (matchCands, SplitCtx (cPsi, cPhi_patt) :: splitCands) 
    | (LF.DDec (cPsi', LF.TypDecl(_, tA)) , LF.DDec (cPhi', LF.TypDecl (_, tB))) -> 
	 let (mC , sC) = pre_match_dctx cD cD_p cPsi' cPhi' matchCands splitCands in  
	   pre_match_typ cD cD_p (cPsi', (tA, S.LF.id)) (cPhi', (tB, S.LF.id)) mC sC 
    | (_ , _ ) -> raise (Error (Syntax.Loc.ghost, MatchError "Ctx mismatch"))
  end




(* ********************************************************************************)
(* getSchemaElems : LF.mctx -> LF.dctx -> LF.sch_elem list
 * getSchemaElems cO cPsi
 *    = [F_1, ..., F_n]   if cPsi has a context variable of schema F_1 + ... + F_n
 *    = []                if cPsi has no context variable
 *)
let getSchemaElems cD cPsi =  match Context.ctxVar cPsi with
  | None -> []
  | Some psi ->
      let LF.Schema elems = 
	Store.Cid.Schema.get_schema 
	  (Context.lookupCtxVarSchema cD psi) 
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
let rec genSpine cD cPsi sA tP = begin match Whnf.whnfTyp sA with 
  | (LF.PiTyp ((LF.TypDecl (_, tA) , _ ), tB), s) ->  
      (* cPsi' |- Pi x:A.B <= typ
         cPsi  |- s <= cPsi'
         cPsi  |- tN <= [s]tA
         cPsi |- tN . s <= cPsi', x:A
      *)
(*      let tN         = Whnf.etaExpandMV cPsi (tA,s) idSub in     *)
      let tN = etaExpandMVstr cD cPsi (tA,s)  in  
      let _  = dprint (fun () -> "[genSpine] tN = " ^ P.normalToString cD cPsi (tN, S.LF.id) ) in 
      let tS  = genSpine cD cPsi (tB, LF.Dot(LF.Obj(tN), s))  tP  in 				
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
let rec genObj (cD, cPsi, tP) (tH, tA) = 
    (* make a fresh copy of tP[cPsi] *)
    let _ = dprint (fun () -> "[genObj] cD = " ^ P.mctxToString cD) in 
    let _ = dprint (fun () -> "[genObj] " ^ P.dctxToString cD cPsi ^ " |- " 
		      ^ P.typToString cD cPsi (tP, S.LF.id)) in 
    let _ = dprint (fun () -> "[genObj] type of head : " ^ P.typToString cD cPsi (tA, S.LF.id)) in 
    let ms    = Ctxsub.mctxToMSub cD in 
    let _ = dprint (fun () -> " ms = " ^ P.msubToString LF.Empty ms ) in 
    let tP'   = Whnf.cnormTyp (tP, ms) in
    let cPsi' = Whnf.cnormDCtx (cPsi, ms) in 
    let tA'   = Whnf.cnormTyp (Whnf.normTyp (tA, S.LF.id), ms) in 
    let tH'   = Whnf.cnormHead (tH, ms) in 
    let _ = dprint (fun () -> "[genObj] of type : " ^ 
		      P.dctxToString LF.Empty cPsi' ^ " |- " ^ 
		      P.typToString LF.Empty cPsi' (tA', S.LF.id) )      in

    let tM = LF.Root (Syntax.Loc.ghost, tH' , genSpine LF.Empty cPsi' (tA', S.LF.id) tP') in
    let (cD', cPsi', tR, tP', ms') =   
      begin try
	Abstract.abstrCovGoal cPsi'  tM   tP' (Whnf.cnormMSub ms) (* cD0 ; cPsi0 |- tM : tP0 *)
      with Abstract.Error (_, Abstract.LeftoverConstraints) as e ->
	(print_string ("WARNING: Encountered left-over constraints in higher-order unification\n");
	 print_string ("Coverage goal : " ^ P.normalToString LF.Empty  cPsi' (tM, S.LF.id) ^ " : " ^ 
			  P.typToString LF.Empty cPsi' (tP', S.LF.id) ^ "\n");
	 raise e)
      end
      in 
    let (cPsi', tR', tP')  = (Whnf.normDCtx cPsi', Whnf.norm (tR, S.LF.id), Whnf.normTyp (tP', S.LF.id)) in 
      (cD' , CovGoal (cPsi', tR', (tP', S.LF.id)), ms')

let rec genAllObj cg tHtA_list = match tHtA_list with 
  | [] -> []
  | tH_tA :: tHAlist -> 
      begin try 
	let cg' = genObj cg tH_tA in 
	   cg' :: genAllObj cg tHAlist 
      with U.Unify _ -> genAllObj cg tHAlist 
	| _ -> genAllObj cg tHAlist 
      end 

let rec genConst  ((cD, cPsi, LF.Atom (_, a, _tS)) as cg) = 
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

let rec genBVar ((_cD, cPsi, _tP) as cg) = 
  let k = Context.dctxLength cPsi in

  let rec genBVarCovGoals i  = if i = (k+1) then []
   else 
    let LF.TypDecl (_ , tA)  = Context.ctxDec cPsi i in   (* x_i : tA   in   cPsi *)
    let tH_tA_list   = genHeads (LF.BVar i , tA) in 
    let cov_goals_i  = genAllObj  cg tH_tA_list in
      cov_goals_i @ genBVarCovGoals (i+1)
  in 
    genBVarCovGoals 1 


let rec genPVar (cD, cPsi, tP)   = 
  let _ = dprint (fun () -> "Generate PVar Cases .. \n" ^ 
		    P.mctxToString cD ^ " ; " ^ 
		    P.dctxToString cD cPsi ^ 
		    "\n      |- " ^ P.typToString cD cPsi (tP, S.LF.id)) in 
  begin
    match Context.ctxVar cPsi with 
    | None -> (dprint (fun () -> "[genPVar] No PVar cases because there is no ctx-var\n"); [])
    | Some psi -> 
	let _ = dprint (fun () -> "Generate PVar ") in 
	let cvar_psi = LF.CtxVar psi in
	let selems = getSchemaElems cD cPsi in

	let rec genPVarCovGoals elems = match elems with
	  | [] -> []
	  | LF.SchElem (decls, trec) :: elems -> 
	      let pv_list = genPVarCovGoals elems in 
		
	      let cPhi             = Context.projectCtxIntoDctx decls in
	      let _ = dprint (fun () -> "call [ctxToSub_mclosed]") in 
	      let (cD', s, offset) = Ctxsub.ctxToSub_mclosed cD  cvar_psi cPhi in 
		(* cO ; cD' ; psi |- [s]trec  *)
		(* cO ; cD'  |- (cPsi, mshift offset) 
		   cO ; cD' ; (cPsi, mshift offset) |- (tP, mshift offset)
		*)
	      let trec'     = Whnf.normTypRec (trec, s) in 
		
	      let (pdecl, tA)  = (match trec' with 
				      LF.SigmaLast tA -> 
					(LF.PDecl(new_parameter_name "p@", 
						  tA, Whnf.cnormDCtx (cvar_psi, LF.MShift offset)) , tA)
				    | LF.SigmaElem _  -> 
					(LF.PDecl (new_parameter_name "p@", 
						   LF.Sigma trec', Whnf.cnormDCtx (cvar_psi, LF.MShift offset)) , LF.Sigma trec')
			   ) in 
		
	      let cD'_pdecl = LF.Dec(cD', pdecl) in
	      let cPsi'  = Whnf.cnormDCtx (cPsi, LF.MShift (offset + 1)) in 
	      let tP'    = Whnf.cnormTyp (tP, LF.MShift (offset + 1)) in 
	      let cg'    = (cD'_pdecl, cPsi', tP') in 
		
	      let _      = dprint (fun () -> "cg ' = \n  " ^ P.mctxToString cD'_pdecl ^ ";\n  " ^ 
				     P.dctxToString cD'_pdecl cPsi' ^ "\n  |- \n   " ^ 
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
	      let _ = dprint (fun () -> "[genHeads] done") in 
	      let cg_list    = genAllObj cg' (tH_tA_list) in
	      let _ = dprint (fun () -> match cg_list with [] ->
				"[genPVarCovGoals] " ^ " NO PVar cases " | _ -> "") in 
              (* each cg in cg_list:    (cO_k,cD_k), ms_k   
                 where cD_k |- ms_k : cD'_pdcl     
                 we need however:    cD_k |- ms'_k : cD 
                                                  
                    mcomp (MShift (offset + 1) ms_k
               *)
	      let cg_list'    = List.map (fun (cD',cg, ms) -> (cD', cg, Whnf.mcomp (LF.MShift (offset + 1)) ms)) cg_list in
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

let rec genBCovGoals ((cD, cPsi, tA) as cov_problem) =  match tA  with
  | LF.Atom _ -> 
      genPVar cov_problem @
      genBVar cov_problem 
  | LF.Sigma trec -> 
      raise Error.NotImplemented
  | LF.PiTyp ((tdecl, dep ) , tA) -> 
      let x = match tdecl with LF.TypDecl (x, _ ) -> x | LF.TypDeclOpt x -> x in 
      let cg_list = genBCovGoals (cD, LF.DDec (cPsi, tdecl), tA) in 
	List.map (fun (cD',cg, ms) -> 
		    let CovGoal (LF.DDec(cPsi', tdecl'), tM, sA) = cg in 
		    let cg' = CovGoal (cPsi', LF.Lam (Syntax.Loc.ghost, x, tM), 
				       (LF.PiTyp ((tdecl' , dep), LF.TClo(sA)), S.LF.id)) in 
		      (cD', cg', ms))
	  cg_list


let rec genCovGoals (((cD, cPsi, tA) as cov_problem) : (LF.mctx * LF.dctx * LF.typ) )
 =  match tA  with
  | LF.Atom _ -> 
      let g_pv = genPVar cov_problem in (* (cD', cg, ms) list *)
      let _ = dprint (fun () -> "[genCovGoals] generated pvar cases\n") in 
      let g_bv = genBVar cov_problem in
      let _ = dprint (fun () -> "[genCovGoals] generated bvar cases\n") in 
	g_pv @ g_bv @ genConst cov_problem

  | LF.PiTyp ((tdecl, dep ) , tB) -> 
      let cov_goals = genCovGoals (cD, LF.DDec (cPsi, tdecl), tB) in 
      let LF.TypDecl (x, _ ) = tdecl in 
	List.map (function (cD', cg, ms) -> 
		    let CovGoal (LF.DDec (cPsi', tdecl'), tM, sA) = cg in 
		      (cD', CovGoal (cPsi', LF.Lam (Syntax.Loc.ghost, x, tM), 
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
  with Abstract.Error _ -> (print_endline "Unable to prove remaining open coverage goals trivially empty due to higher-order constraints." ; false)
  end

let rec solve' cD (matchCand, ms) cD_p mCands sCands = match matchCand with 
  | [] -> (match sCands with []  -> Solved
	     | _ -> PossSolvable (Cand (cD_p , mCands, sCands)))
  | mc :: mCands ->
      begin match mc with
	| Eqn (CovGoal (cPsi, tR, sA) , NeutPatt (cPsi_p, tR_p, sA_p)) -> 
	  let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in 
	  let tR_p'   = Whnf.cnorm (tR_p, ms) in 
	  let tA_p'   = Whnf.cnormTyp (Whnf.normTyp sA_p,  ms) in 
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
	      solve' cD (mCands, ms) cD_p (mc::mCands) sCands 
	    with
	      (* should this case betaken care of  during pre_match phase ? *)
	      |U.Unify "Context clash" -> 
		 let _ = print_string "Unification of pre-solved equation failed due to context mis-match - initiate context matching" in 
	      	let sc = SplitCtx (cPsi , cPsi_p) in 
		let _ = dprint (fun () -> "Initiate context splitting: " ^ P.dctxToString cD cPsi ^ " == " ^ 
		  P.dctxToString cD cPsi_p' ^ " \n") in 
		  solve' cD (mCands, ms) cD_p mCands (sc::sCands) 
	      | U.Unify msg -> 
	      if U.unresolvedGlobalCnstrs () then 
		let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND") in
		let sc = Split (CovGoal (cPsi, tR, sA) , NeutPatt (cPsi_p, tR_p, sA_p)) in 
		  solve' cD (mCands, ms) cD_p mCands (sc::sCands)
	      else 
		let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ " \n CONSTRAINT NOT SOLVABLE\n") in
		  NotSolvable
	    end

	| EqnCtx (cPsi, cPsi_p) -> 
	    let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in 
	      begin try
		U.unifyDCtx cD cPsi cPsi_p' ;
		solve' cD (mCands, ms) cD_p (mc::mCands) sCands 
	      with U.Unify msg -> 
		  let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ) in
		    NotSolvable
	      end
      end


let rec solve cD cD_p matchCand = match matchCand with 
  | [] -> Solved
  | mc :: mCands ->
  (*  mc =  Eqn (_  , NeutPatt (_, _, _)) ->  *)
      let ms = Ctxsub.mctxToMMSub cD cD_p in 
	solve' cD (matchCand ,  ms) cD_p [] []

(* refineSplits matchL splitL ms = (matchL', splitL')

 if   cD' |- ms : cD 
      cD' |- matchL
      cD  |- splitL 
then 
      cD' |- matchL'    and matchL @ matchL0 = matchL'
      cD' |- splitL'    and splitL' is the refined splitL
*)
let rec refineSplits (cD:LF.mctx) (cD_p:LF.mctx) matchL splitL ms = match splitL with
  | [] -> (matchL , [] )
  | Split (CovGoal (cPsi, tR, sA) , patt ) :: splits -> 
      (let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in 
      let tA     = Whnf.normTyp sA in 

      let (cPsi, tR, tA) = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in

      let (CovGoal (cPsi', tR', sA')  as covG)   = CovGoal (cPsi, tR, (tA, S.LF.id))  in 
      (* let NeutPatt(cPhi, _tN, sB') = patt in *)
      (* let (mL', sL') = pre_match_typ cD cD_p (cPsi, sA') (cPhi, sB') matchL' splitL' in   *) 
      (* let (mL', sL') = pre_match_dctx cD cD_p cPsi cPhi matchL' splitL' in *)
      let result = pre_match cD cD_p covG patt matchL' splitL' in 
	result
      )
  | SplitCtx (cPsi, cPsi_patt ) :: splits -> 
      let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in 
      let cPsi' = Whnf.cnormDCtx (cPsi, ms) in 
	pre_match_dctx cD  cD_p cPsi' cPsi_patt matchL' splitL' 

(* cnormEqn matchL ms = [ms]matchL

   if cD |- matchL 
      cD' |- ms : cD 
  then 
      cD' |- [ms]matchL 
*)
let rec cnormEqn matchL ms = begin match matchL with
  | [] -> []
  | (Eqn (CovGoal (cPsi, tR, sA) , patt ) :: matchL') -> 
      let tA     = Whnf.normTyp sA in 

      let (cPsi, tR, tA) = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in 

     
      let covG0   = CovGoal (cPsi, tR, (tA, S.LF.id)) in 

      let matchL0 = cnormEqn matchL' ms in 
	Eqn (covG0, patt) :: matchL0
end

(* refine_covprob (cD_cg, ms) cand = [ms]cand

if 
   cD |- ms : cD'
   cO' ; cD' |- cand 
then
   cO ; cD |- [ms]cand

*)

let rec refine_cand (cD', ms) (cD, Cand (cD_p, matchL, splitL)) = 
  let matchL' = cnormEqn matchL  ms in 
  let _ = dprint (fun () -> "[refine_cand] matchL' = " ^ eqnsToString cD' cD_p matchL' ) in 
  let (matchL0,splitL0) = refineSplits cD' cD_p matchL' splitL ms in
    Cand (cD_p, matchL0, splitL0)

let rec refine_candidates (cD', ms) (cD, candidates) = match candidates with
  | [] -> []
  | cand :: cands -> 
      begin try 
	let cand' = refine_cand (cD', ms) (cD, cand)  in
	let _ = dprint (fun () -> "REFINED CANDIDATE \n" ^ candToString cD' cand')  in
	  cand' :: refine_candidates (cD', ms) (cD, cands)
      with 
	  Error (_, MatchError _) -> refine_candidates (cD, ms) (cD , cands)
      end


let rec refine_covproblem cov_goals ( (cD, candidates, (cPhi, tM) ) as cov_problem ) = 
  match cov_goals with 
  | [] -> []
  | (TermCandidate ((cD_cg, _, ms) as cg)) :: cgs  -> 
       let _ = dprint (fun () -> "[Consider coverage goal] \n     " ^ covGoalsToString [cg] ) in 
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^ 
			  " candidates.\n");
		dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms ))   in 

       let candidates' = refine_candidates (cD_cg, ms) (cD, candidates) in 

       let _ =  dprint (fun () -> "[refine_candidates] DONE : There are
			    remaining #refined candidates = " ^ string_of_int  (List.length candidates')) in 
       let tM'     = Whnf.cnorm (tM, ms) in 
       let cPhi'   = Whnf.cnormDCtx (cPhi, ms) in 
	 (match candidates' with
	   | [] -> (dprint (fun () -> "[OPEN COVERAGE GOAL] " ^ covGoalsToString [cg] ) ; 
	            open_cov_goals := (cD_cg, cPhi', tM')::!open_cov_goals ; 
		    refine_covproblem cgs cov_problem )
	   | _  -> 
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates') ^ 
			 " refined candidates for " ^ P.normalToString cD_cg cPhi' (tM', S.LF.id) ^ "\n"); 
	       dprint (fun () -> candidatesToString (cD_cg, candidates', (cPhi', tM'))) ; 
	       ((cD_cg, candidates', (cPhi', tM')) :: refine_covproblem cgs cov_problem) ) 
	 )

  | CtxCandidate (cD_cg, cPhi_r, ms) :: cgs  -> 
       let _ = dprint (fun () -> "[Consider context goal] \n     " ^
			 P.dctxToString cD_cg cPhi_r) in  
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^ 
			  " candidates.\n");
		dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms ))   in  

       let candidates' = refine_candidates (cD_cg, ms) (cD, candidates) in 

       let _ =  dprint (fun () -> "[refine_candidates] DONE : There are
			    remaining #refined candidates = " ^ 
			  string_of_int (List.length candidates')) in  


         let tM'     = Whnf.cnorm (tM, ms)  in 
         let cPhi'   = Whnf.cnormDCtx (cPhi,ms) in 
	 (* cD |- cPhi     and     cD0, cD |- ms : cD ? *)

	 (match candidates' with 
	   | [] -> (dprint (fun () -> "[OPEN CONTEXT GOAL] " ^ P.dctxToString cD_cg cPhi_r) ; 
		    dprint (fun () -> "[OPEN COVERAGE GOAL] " ^ P.dctxToString cD_cg cPhi' ^ " . " ^  
			      P.normalToString cD_cg cPhi' (tM', S.LF.id) );
	            open_cov_goals := (cD_cg, cPhi', tM')::!open_cov_goals ;  
		    refine_covproblem cgs cov_problem )  
	   | _  -> 
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates') ^ 
			 " refined candidates for " ^ P.normalToString cD_cg cPhi' (tM', S.LF.id) ^ "\n");  
	       dprint (fun () -> candidatesToString (cD_cg, candidates', (cPhi', tM'))) ; 
	       ((cD_cg, candidates', (cPhi', tM')) :: refine_covproblem cgs cov_problem) ) 
	 )

let rec check_empty_pattern k candidates = match candidates with
  | [] -> []
  | Cand (cD_p, ml, sl) :: cands -> 
      let sl' = List.filter (fun (Split (CovGoal (_cPsi, tR, _sA) , patt)) -> 
			       match patt with 
				 | EmptyPatt (_cPhi, _sB) -> 
				     (match tR with 
					|LF.Root (_, LF.MVar (LF.Offset k', _ ), LF.Nil ) -> not (k = k' )
					| _ -> true)
				 | _ -> true )
	sl in 
	Cand (cD_p, ml, sl') :: check_empty_pattern k cands


(* ************************************************************************************* *)

 let rec addToCCtx cO cO_tail = match cO_tail with
  | [] -> cO 
  | (LF.CDecl _  as cdec) :: cO_tail -> 
	addToCCtx (LF.Dec(cO, cdec)) cO_tail


let rec addToMCtx cD (cD_tail, ms) = match cD_tail with
  | [] -> (cD , ms)
  | LF.MDecl (u, tA, cPsi) :: cD_tail -> 
      let mdec = LF.MDecl(u, Whnf.cnormTyp (tA, ms), Whnf.cnormDCtx (cPsi, ms)) in 
	addToMCtx (LF.Dec (cD, mdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.PDecl (u, tA, cPsi) :: cD_tail -> 
      let pdec = LF.PDecl(u, Whnf.cnormTyp (tA, ms), Whnf.cnormDCtx (cPsi, ms)) in 
	addToMCtx (LF.Dec (cD, pdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | cdecl :: cD_tail -> 
      addToMCtx (LF.Dec (cD, cdecl)) (cD_tail, Whnf.mvar_dot1 ms)


let rec append cD cD_tail = match cD_tail with
  | [] -> cD 
  | dcl :: cD_tail -> append (LF.Dec (cD, dcl)) cD_tail

(* append (cO, cO_tail) cD1 (cD2 (cpsi, tB)) = (cD1, cD2') 
   
   if  cO, cO_tail |- cD2 mctx
       cO, cO_tail |- cD1 mctx
       cO, cO_tail ; cD1 ; cpsi |- tB 
   then
       cO |- cD1, [psi,x:tB / psi]cD2' mctx
   
*)
(* let rec append cD1 (cD2, (cpsi, tB), d) = match cD2 with
  | LF.Empty ->  cD1

  | LF.Dec (cD2', dec) ->
      let cD1' = append cD1 (cD2', (cpsi, tB), d-1) in
      let tB'  = Whnf.cnormTyp (tB, LF.MShift (d-1)) in 
      (* cD1 *)
      let cs   = LF.MDot (LF.CObj(LF.DDec (cpsi, LF.TypDecl (new_bvar_name "@x", tB'))), LF.MShift k) in 
      let dec' = match dec with 
	| LF.MDecl(u, tA, cPhi) -> LF.MDecl(u, Ctxsub.ctxnorm_typ (tA, cs), Ctxsub.ctxnorm_dctx (cPhi, cs)) 
	| LF.PDecl(u, tA, cPhi) -> LF.PDecl(u, Ctxsub.ctxnorm_typ (tA, cs), Ctxsub.ctxnorm_dctx (cPhi, cs)) 
      in
        LF.Dec (cD1', dec')
*)

(* cD0, cD |- id(cD) : cD *) 
let rec gen_mid cD0 cD = match cD with 
  | LF.Empty -> LF.MShift (Context.length cD0) 
  | LF.Dec(cD, _mdec) -> 
      let ms' = gen_mid cD0 cD (* cD0, cD |- ms' : cD *)
      in LF.MDot (LF.MV 1, Whnf.mcomp ms' (LF.MShift 1))


(*
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
*)
  (* decTomdec cD' cPhi = (cD'' , s) 
    where
    cD'' = cD', cD0   
    cD'' ; cpsi |- s : cPhi
    x:A in cPhi iff x:A[cpsi] in cD0

    and   cO'' |- cD'' mctx 
  *)
  let rec decTomdec cD' ((LF.CtxVar (LF.CtxOffset k)) as cpsi) (d, decls) = match decls with
    | LF.Empty ->   (cD', S.LF.id)   
    | LF.Dec(decls, dec) -> 
	let LF.TypDecl (x, tA) = dec in 
        (* . ; decls |- tA : type            *)
        (*  cD' ; cpsi, @x: _  |- s' : decls         *)
	let (cD'', s')  = decTomdec cD' cpsi (d-1, decls) in   
	let (cPsi, (LF.Atom (_ , a, _tS) as tP, s)) = lower (LF.CtxVar (LF.CtxOffset (k+d))) (tA, s') in 
	let _ = dprint (fun () -> "[decTomdec] cPsi = " ^ P.dctxToString cD''  cPsi) in
	let _ = dprint (fun () -> "[decTomdec] tP = " ^ P.typToString cD'' cPsi (tP, S.LF.id)) in
	let _ = dprint (fun () -> "[decTomdec] s' = " ^ P.subToString cD''  LF.Null s')in
	(* bp : Context substitution associated with declaration is off by 1 *)  
	let (ss', cPsi') = Subord.thin' cD''  a cPsi in  
	let _ = dprint (fun () -> "[Subord.thin'] ss' = " ^ P.subToString cD'' cPsi' ss') in
        (* cPsi |- ss' : cPsi' *)  
        let ssi' = S.LF.invert ss' in
        (* cPsi' |- ssi : cPsi *) 
	let ssi = S.LF.comp s ssi' in 
	let _ = dprint (fun () -> "[Subord.thin'] ss' = " ^ P.subToString cD'' cPsi' ssi) in
	let _ = dprint (fun () -> "[genCtx] generated mvar of type " ^ P.dctxToString cD'' cPsi'  ^ " |- " ^ 
			  P.typToString cD'' cPsi' (tP, ssi)) in 	  
	let mdec = LF.MDecl (x, LF.TClo(tP,ssi), cPsi') in 
	let mv   = LF.Root(Syntax.Loc.ghost, LF.MVar(LF.Offset 1, Whnf.cnormSub  (ss', LF.MShift 1)), LF.Nil) in 
	  (LF.Dec (cD'', mdec) , LF.Dot(LF.Obj mv, Whnf.cnormSub (s', LF.MShift 1)))

  (* genCtx elems = ctx_goal_list 

     for each ctx_goal in ctx_goal_list . 
        ctx_goal = (cD_i, cPsi_i, ms_i)  s.t.
        cO ; cD_i |- ms_i   : cD
        cO ; cD_i |- cPsi_i : ctx
  *)
  let rec genCtx  (LF.Dec (cD', LF.CDecl _ ) as cD) cpsi elems  = begin match elems with 
    | [] -> [] 
    | LF.SchElem (decls, trec) :: elems -> 
	let cPsi_list = genCtx cD cpsi elems in 
	let d = Context.length decls in 
	let (cD0, s)   = decTomdec cD cpsi (d-1, decls) in
	let _ = dprint (fun () -> "[genCtx] s = " ^ P.subToString cD0 cpsi s) in 
	let cpsi' = LF.CtxVar (LF.CtxOffset (d+1)) in 
         (* cD0 = cD, decls *)
	let tA = match trec with LF.SigmaLast tA -> LF.TClo (tA, s) | _ -> LF.TClo(LF.Sigma trec, s) in  
	let _ = dprint (fun () -> "[genCtx] tA = " ^ P.typToString cD0 cpsi' (tA, S.LF.id)) in
	  (* cD0 ; cpsi |- tA : type *)
	let ms = gen_mid cD0 cD' in 
        (* cD0,cD |- ms : cD 
              cD' |- cPsi' ctx *)
	let cPsi'      = LF.DDec (cpsi', LF.TypDecl (new_bvar_name "@x" , tA)) in 

	let _ = dprint (fun () -> "[genCtx] " ^  P.dctxToString cD0 cPsi' ^ "\n") in 
	let _ = dprint (fun () -> "ms = " ^ P.msubToString cD0 ms ^ "\n") in 
	let _ = dprint (fun () -> "cD0 = " ^ P.mctxToString cD0 ^ "\n") in 
	let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD ^ "\n") in 
	   (cD0, cPsi', ms) :: cPsi_list 
  end


(* genCtxGooals cD (psi:W) = goal_list 

   such that  
   goal-list = 
   [cD, psi:schema, cD' |- psi, x:s_elem_1 , ...  where cD' = FMV(s_elem1)
    cD, psi:schema, cD' |- psi, x:s_elem_n , ...  where cD' = FMV(s_elemn)
    cD                  |- .  
   ]
*)
let rec genCtxGoals cD (LF.CDecl(x, schema_cid, dep)) =   
  let LF.Schema elems = Store.Cid.Schema.get_schema schema_cid in 
  let cD'  = LF.Dec(cD, LF.CDecl(x, schema_cid, dep)) in 
    genCtx cD' (LF.CtxVar (LF.CtxOffset 1)) elems  


(* Find mvar to split on *)


(* let rec mdot  ms k = match k with
  | 0 -> ms
  | k -> mdot (Whnf.mvar_dot1 ms) (k-1)
*)

let genCGoals (cD':LF.mctx) mdec = match mdec with
  | LF.MDecl (_u, tA, cPsi) -> 
      let _ = dprint (fun () -> "[SPLIT] CovGoal : " ^ P.dctxToString cD' cPsi ^ " . " ^ 
			P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in 
      let dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
	(genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) , dep0) 
  | LF.PDecl (_u, tA, cPsi) -> 
      let _ = dprint (fun () -> "[SPLIT] CovGoal (PVAR): " ^ P.dctxToString cD' cPsi ^ " . " ^ 
			P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in 
      let dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
      (* bp : This may potentially even loop! ; 
	 but this could initiate a potential split of PV including splitting the context 
	 g |- #A  should result in  g',x|- x   g',x|- #q 
         in this implementation, we assume that the context split has been done separetely,
	 and hence we would only loop if we were to split #p (and initiate another context split)
      *)
	(genBCovGoals (cD', cPsi, tA), dep0)  
	(* raise Error.NotImplemented *)


let rec best_ctx_cand (cD, cv_list) k cD_tail = match (cv_list, cD)  with 
  | [], _  -> NoCandidate
  | [LF.CtxOffset j] , LF.Dec (cD', cd) -> 
      if j = k then 
	let ctx_goals = genCtxGoals cD' cd in  
	let ctx_goals' = List.map (fun (cD', cPhi, ms) -> 
				     (* cD' |- ms : cD *)
				     let ms' = LF.MDot (LF.CObj (cPhi),  ms) in  
				     let k = List.length cD_tail in 
				     let (cD'', ms0) = addToMCtx cD' (cD_tail, ms') in 
				     let _ = dprint (fun () -> "[ctx_goal] = " ^ 
						       P.mctxToString cD'' ^ " \n |- \n" ^ 
						       P.msubToString cD'' ms0 ^
						       " : " ^ P.mctxToString (append cD cD_tail)) in 
				       CtxCandidate (cD'' , Whnf.cnormDCtx (cPhi, LF.MShift k),  ms0 )
                                  ) 
          ctx_goals in 
            SomeCtxCands ctx_goals' 
      else 
	best_ctx_cand (* (cO, cv_list)*) (cD', cv_list) (k+1) (cd::cD_tail)


let rec best_cand (* (cO,cv_list) *) (cD, mv_list) k cD_tail  = 
match (mv_list, cD) with 
  | ([] , _ )  -> NoCandidate
  | (LF.Offset j :: mvlist' ,  LF.Dec (cD', md))->        
      if k = j then 
	begin try
	  let (cov_goals' , dep0) =  genCGoals cD' md  in
	  let cov_goals0 = List.map (fun (cD', cg, ms) -> 
				       let CovGoal (cPsi', tR, sA') = cg in 
				       let ms' = LF.MDot (LF.MObj ( Context.dctxToHat cPsi' , tR),  ms) in  
				       let k = List.length cD_tail in 
				       let (cD'', ms0) = addToMCtx cD' (cD_tail, ms') in 
				       let cg' = CovGoal (Whnf.cnormDCtx (cPsi', LF.MShift k) , 
							  Whnf.cnorm (tR, LF.MShift k) ,
							  (Whnf.cnormTyp (Whnf.normTyp sA' , LF.MShift k), S.LF.id)) in 
					 TermCandidate (cD'' , cg',  ms0 )				   
				    )
                           cov_goals'
	  in 
	    
	    match best_cand (* (cO, cv_list)*) (cD', mvlist') (k+1) (md::cD_tail) with 
	      | NoCandidate -> SomeTermCands (dep0, cov_goals0)
	      | SomeTermCands (dep, cov_goals) -> 
		  (match (dep, dep0) with 
		     | (Dependent,  Atomic) -> SomeTermCands (dep, cov_goals)
		     | (Atomic,  Dependent) -> SomeTermCands (dep0, cov_goals0)
		     | ( _       , _      ) -> (if  List.length cov_goals < List.length cov_goals0 
						then SomeTermCands (dep, cov_goals) else SomeTermCands (dep0, cov_goals0 )
					       )	
		  )
	  with Abstract.Error (_, Abstract.LeftoverConstraints) ->
	    (print_endline ("WARNING: Encountered left-over constraints in higher-order unification.\n\
                             Try another candidate.");
	     best_cand (* (cO,cv_list)*) (cD', mvlist') (k+1) (md::cD_tail))
	end
      else 
	best_cand (* (cO, cv_list)*) (cD', mv_list) (k+1) (md::cD_tail)



(* best_candidate cO cD = cov_goals

   cov_goals is a list of coverage goals   CovGoal (cOD', cg, ms) 

   where

   cg = CovGoal (cPsi, tR, sA) and   cOD' |- ms : cO;cD 

*)

let rec mvInSplitCand cD vlist candidates = match candidates with
  | [] -> vlist
  | Cand(_, _ , sl) :: cands -> 
      mvInSplitCand cD (mvInSplit cD vlist sl) cands
      
and mvInSplit cD vlist slist = match slist with
  | [] -> vlist
  | Split (CovGoal (_, LF.Root (_ , LF.MVar (u, _ ) , _ ), _ ), _ ) :: sl -> 
      let (cvlist , mvlist) = vlist in 
      if List.mem u mvlist then 
	mvInSplit cD vlist sl 
      else mvInSplit cD (cvlist, (u::mvlist)) sl

  | Split (CovGoal (_, LF.Root (_ , LF.PVar (LF.Offset k, _ ) , _ ), _ ), _ ) :: sl -> 
      let (cvlist , mvlist) = vlist in 
      if List.mem (LF.Offset k) mvlist then 
	mvInSplit cD vlist sl 
      else (* mvInSplit cD (cvlist, (p::mvlist)) sl *)
	(match Whnf.mctxPDec cD k with 
	   | (_, _tA, LF.CtxVar _ ) -> 	mvInSplit cD (cvlist, (mvlist)) sl
	   | _ -> 	mvInSplit cD (cvlist, (LF.Offset k)::mvlist) sl)



  | Split (CovGoal (_, LF.Root (_ , LF.Proj (_ , _ ), _tS), _tA) as cg , patt) :: sl ->  
      dprint (fun () -> "SPLIT CAND (SIGMA) : " ^ covGoalToString cD cg ^ " == " ^ 
		 pattToString cD patt ) ; 
      mvInSplit cD vlist sl 

  | SplitCtx (LF.CtxVar psi, cPhi) :: sl -> 
      let (cvlist , mvlist) = vlist in 
(*	mvInSplit cD (psi::cvlist, mvlist) sl  *)
	if List.mem psi cvlist then 
	mvInSplit cD (cvlist, mvlist) sl 
      else mvInSplit cD (psi::cvlist, mvlist) sl




let rec best_split_candidate cD candidates = 
  (* assume candidates are non-empty *)
  let (cvsplit_list, mvsplit_list)  = mvInSplitCand cD ([], []) candidates in 
  let mv_list_sorted = List.sort (fun (LF.Offset k) -> fun (LF.Offset k') -> 
				    if k' < k then 1 else (if k' = k then 0 else -1)) 
                                 mvsplit_list in 
  let cv_list_sorted = List.sort (fun (LF.CtxOffset k) -> fun (LF.CtxOffset k') -> 
				    if k' < k then 1 else (if k' = k then 0 else -1)) 
                                 cvsplit_list in 

  let _ = dprint (fun () -> "SHOW SPLIT CANIDATE LIST " ^ mvlistToString mv_list_sorted ) in  
   if cv_list_sorted = [] then    
     best_cand (cD, mv_list_sorted) 1 [] 
   else
     (dprint (fun () -> "Context Split possible\n") ;
      best_ctx_cand (cD, cv_list_sorted) 1 [])


(* ************************************************************************************* *)

let rec refine ( (cD, candidates, (cPhi,tM)) as cov_problem )  = 
  begin match cD with
    | LF.Empty  -> 
	((* print_string (candidatesToString cov_problem ) ; *)
	 open_cov_goals := (cD, cPhi, tM)::!open_cov_goals ; 
	 raise (Error (Syntax.Loc.ghost, NothingToRefine))
	 (* [] *))
	(* raise (Error "Nothing to refine"))*)
    | _  -> 
	let cov_goals' = best_split_candidate cD candidates in 
	let _ = dprint (fun () -> "[Original candidates] \n" ^ candidatesToString cov_problem ) in
	  begin match (cov_goals', candidates ) with
	    | (SomeCtxCands ctx_goals, [] )  ->  []
	    | (SomeCtxCands ctx_goals,  _ )  -> (* bp : TODO refine_ctx_covproblem ctx_goals cov_problem *)
(*		 raise (Error "Context refinment not implemented yet") *)
  		  refine_covproblem ctx_goals cov_problem	
	    | (SomeTermCands (_, []), [])  -> [] 
	    | (SomeTermCands (_, []), _ )  -> [(cD, check_empty_pattern 1 candidates, (cPhi, tM ) )]
	    | (SomeTermCands (_, cgoals), _ )  -> 
		let _ = dprint (fun () -> 
				  let cgs = List.map (fun (TermCandidate cg) -> cg) cgoals in 
				    "[Generated coverage goals] \n     " ^ covGoalsToString cgs ) in 
  		  refine_covproblem cgoals cov_problem	
	    | (NoCandidate,   [] ) -> []
	    | (NoCandidate, _    ) -> (open_cov_goals := (cD, cPhi, tM) :: !open_cov_goals;[])
(*		let _ = dprint (fun () -> "No Candidates found: Remaining Candidates : \n" ^ 
				  candidatesToString (cD, candidates, (cPhi, tM) )) in
		raise (Error (Syntax.Loc.ghost, NoCoverageGoalsGenerated)) *)
	  end 
  end 
	
let rec check_all f l = (match l with
  | [] -> ()
  | h::t -> 
      ((try f h with
	  Error (_, MatchError _)  -> dprint (fun () ->  "MATCH ERROR"  )
        | Error (_, NothingToRefine)  -> dprint (fun () ->  "Nothing to refine ERROR" )); (* ??? *)
       check_all f t )
			)
(* At least one of the candidates in cand_list must be solvable,
   i.e. splitCand = []  and matchCand are solvable  
*)

	    

let rec check_covproblem cov_problem = 
  let ( cD , candidates, cg) = cov_problem in 
  let rec existsCandidate candidates nCands open_cg =  match candidates with
    | [] -> 
	let cov_prob' = ( cD, nCands, cg)  in 
	  (* there were candidates – refine coverage problem *)
	  open_cov_goals := open_cg @ !open_cov_goals;
	  check_coverage (refine cov_prob')
    | ((Cand (cD_p, matchCand, splitCand )) as c) :: cands ->  
	(match splitCand with 
	   |  [] -> 
		let ( cD, _candidates, (cPhi, tM)) = cov_problem in 
		let _ = dprint (fun () -> "Check whether " ^ P.dctxToString  cD  cPhi ^ " |- " 
				  ^ P.normalToString cD cPhi (tM, S.LF.id) ^
				  " is covered?\n") in 
		(match solve cD cD_p matchCand with 
		   | Solved -> (* No new splitting candidates and all match
				  candidates are satisfied *) 
		       let ( cD , _ , (cPhi, tM)) = cov_problem in 
			 dprint (fun () -> "[check_covproblem] COVERED " ^ P.dctxToString cD
				   cPhi ^ " |- " ^ P.normalToString cD cPhi (tM, S.LF.id)) ; 
		       (* Coverage succeeds *)   ()
		   | PossSolvable cand -> 
		       (* Some equations in matchCand cannot be solved by hounif;
			  they will be resurrected as new splitting candidates *)
		       existsCandidate cands (cand :: nCands) open_cg
		   | NotSolvable -> (* match candidates were not solvable; this candidate gives rise to coverage failure ? *)
		       let (cD , _candidates, (cPhi, tM)) = cov_problem in 
		       let open_goal = (cD, cPhi,  tM) in 
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


let rec extract_patterns (cPhi, tA) branch_patt = match branch_patt with 
  | Branch (loc, cD, _cG, PatMetaObj (loc', pat), ms, _e) -> 
      let (cPsi, tR) = (match pat with 
			  | MetaObjAnn (loc', cPsi, tR) ->
			      (cPsi, tR) (* [ms]cPhi = cPsi *)
			  | MetaObj (loc, phat, tR) -> 
			      (Whnf.cnormDCtx (cPhi, ms), tR)) 
      in
	(cD, NeutPatt (cPsi, tR, (Whnf.cnormTyp (tA, ms), S.LF.id)))
  | EmptyBranch (loc, cD, PatEmpty (loc', cPsi), ms)  -> 
	(cD, EmptyPatt (cPsi, (Whnf.cnormTyp (tA, ms), S.LF.id)))
(*    | Branch (loc, cD, cG, pat, ms, _e) -> 
 | EmptyBranch (loc, cD, patt, ms)  *)

(*  | BranchBox (_cO, cD, (cPsi, NormalPattern (tR, _ ), ms, cs)) -> 
      ( cD,  NeutPatt (cPsi, tR, (Whnf.cnormTyp (Ctxsub.ctxnorm_typ (tA, cs) ,ms), S.LF.id)) )
  | BranchBox (_cO, cD, (cPsi, EmptyPattern, ms, cs)) -> 
      ( cD, EmptyPatt (cPsi, (Whnf.cnormTyp (Ctxsub.ctxnorm_typ (tA, cs),ms), S.LF.id)) )
*)

(* initialize_coverage problem = 
      
*)
let rec initialize_coverage problem = 

  let (tA, cPsi) = problem.ctype in 
  let cD'        = LF.Dec (problem.cD, LF.MDecl(Id.mk_name (Id.NoName), tA, cPsi)) in   
  let mv         = LF.MVar (LF.Offset 1, idSub) in 
  let tM         = LF.Root (Syntax.Loc.ghost, mv, LF.Nil) in 
  let cPsi'      = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
  let sA'        = (Whnf.cnormTyp (tA, LF.MShift 1), S.LF.id) in 
  let covGoal    = CovGoal (cPsi', tM, sA') in 

  let pat_list  = List.map (function b -> extract_patterns (cPsi,tA) b) problem.branches in 

  let rec gen_candidates covGoal patList = match patList with 
    | [] -> [] 
    | (cD, EmptyPatt (cPsi, sA) ) :: plist -> 
	if trivially_empty (cD, cPsi, Whnf.normTyp sA) then 
	  gen_candidates covGoal plist 
	else 
	  raise (Error (Syntax.Loc.ghost, NoCover
	    (Printf.sprintf "\n##   Empty Pattern ##\n   %s\n\n##   Case expression of type : \n##   %s\n##   is not empty.\n\n" 
	       (Syntax.Loc.to_string problem.loc)
	       (P.typToString cD cPsi sA))))
    | (cD, (NeutPatt(cPhi, _tN, sB') as pat)) :: plist -> 
	let _ = dprint (fun () -> "PATTERN : \n     " ^ P.mctxToString cD ^ " |- " ^  pattToString cD pat)  in 

	let ml0, sl0   = pre_match_dctx cD' cD cPsi' cPhi [] [] in 
	let (ml', sl') = pre_match_typ cD' cD (cPsi', sA') (cPhi, sB') ml0 sl0 in  
	let (ml, sl)   = pre_match cD' cD covGoal pat ml' sl' in 
	  Cand (cD, ml, sl) :: gen_candidates covGoal plist 
  in 
  let cand_list =  gen_candidates covGoal pat_list in 

    [ ( cD' , cand_list , (cPsi', tM) ) ] 

let rec check_emptiness cD = match cD with
  | LF.Empty -> false
  | LF.Dec(cD', LF.MDecl (_u, tA, cPsi)) -> 
      begin try
	(match genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> true
	   | _  -> check_emptiness cD'
	) 
      with Abstract.Error (_, msg) ->
	print_endline ("Unable to prove : " ^ P.typToString cD' cPsi (tA, S.LF.id) ^ " to be empty") ;
	print_endline "Try next meta-variable ...";
	check_emptiness cD'
      end 
  | LF.Dec(cD', LF.PDecl (_u, LF.Sigma _ , _cPsi)) -> 
      check_emptiness cD'
  | LF.Dec(cD', LF.PDecl (_u, tA, cPsi)) -> 
      begin try
	(match genBCovGoals (cD' , cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> true
	   | _  -> check_emptiness cD'
	) 
      with Abstract.Error (_, msg) ->
	print_string "Unable to prove given type is empty\n" ; check_emptiness cD'
      end 

  | LF.Dec (cD', LF.CDecl _ ) -> check_emptiness cD'

let rec revisit_opengoals ogoals = begin match ogoals with
  | [] -> ([], [])
  | ((cD, _cPsi, _tM) as og) :: ogoals -> 
      if check_emptiness cD then 
        let (oglist , trivial_list) = revisit_opengoals ogoals in 
	  (oglist, og::trivial_list)
      else 
	let (oglist, trivial_list) = revisit_opengoals ogoals in 
	  (og :: oglist, trivial_list)
end 

let check_coverage_success problem  =  
  Debug.popIndentationLevel ();
  match problem.prag with
    | Pragma.RegularCase -> 
      if !open_cov_goals = [] then 
	(dprint (fun () -> "## COVERS ##");
	 Success)
      else 
	 (* Check if the open coverage goals can be proven to be impossible *)
        Failure (Printf.sprintf "\n##   Case expression doesn't cover: ##\n##   %s\n##   %s\n\n"
                   (Syntax.Loc.to_string problem.loc)
                   ("CASE(S) NOT COVERED :\n" ^ opengoalsToString (!open_cov_goals)))

    | Pragma.PragmaNotCase ->
      if !open_cov_goals = [] then 
	Failure (Printf.sprintf "\n##   Case expression covers : ##\n##   %s\n##\n\n"
                   (Syntax.Loc.to_string problem.loc))
      else begin
	Printf.printf "\n##   Case expression doesn't cover, consistent with \"case ... of %%not\" ##\n##   %s\n##   %s\n\n"
          (Syntax.Loc.to_string problem.loc)
          ("CASE(S) NOT COVERED :\n" ^ opengoalsToString (!open_cov_goals) );
	Success
      end

(* covers problem = ()

  problem  = {loc: loc ; prag : pragma ; 
              cD : LF.mctx ;
              branches ; ctype : tA[cPsi] }

  where   cD ; cPsi |- tA  

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
              ^ Syntax.Loc.to_string problem.loc);

    dprint (fun () -> "Initial coverage problem \n" ^ covproblemsToString cov_problems ) ; 
    
    check_coverage cov_problems ;  (* there exist all cov_problems are solved *) 
    let o_cg         = !open_cov_goals in 
    let r            = List.length  o_cg in 
    let (revisited_og, trivial_og) = revisit_opengoals o_cg in 
    let r'           = List.length (revisited_og) in 

    if r  > r' then 
      (print_endline "\n(Some) coverage goals were trivially proven to be impossible.";
       print_endline ("CASES TRIVIALLY COVERED in line " ^
			 Syntax.Loc.to_string  problem.loc
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
  | Failure message ->
      if !warningOnly then
        Error.addInformation ("WARNING: Cases didn't cover: "  ^ message)
      else
        raise (Error (Syntax.Loc.ghost, NoCover message))



let problems = ref ([] : problem list)

let clear () =
  problems := []

let stage problem =
  problems := problem::!problems

let force f =
  List.map (fun problem -> f (covers problem)) (List.rev !problems)

