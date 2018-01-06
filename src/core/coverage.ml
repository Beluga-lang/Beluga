(** Coverage checker

   @author Brigitte Pientka
*)

(* open Id *)

open Syntax.Int
(* open Store.Cid *)

module Types = Store.Cid.Typ
module Const = Store.Cid.Term

module S = Substitution
module U = Unify.EmptyTrail
module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.NamedRenderer

let idSub  = S.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)


 let (dprint, _) = 
 Debug.makeFunctions (Debug.toFlags [29])


(* let dprint f = print_string ("\n" ^ (f ()) ^ "\n\n")  *)

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
	| NoCover s -> Format.fprintf ppf "\n######   COVERAGE FAILURE: Case expression doesn't cover: ######\n##   %s\n##" s
	| MatchError s -> Format.fprintf ppf "\n######   COVERAGE FAILURE: Case expression doesn't cover: ######\n##  Matching fails due to %s." s
	| NothingToRefine -> Format.pp_print_string ppf "Nothing to refine"
	| NoCoverageGoalsGenerated -> Format.pp_print_string ppf "No coverage goals generated"))

(* Generating meta-variable and parameter variable names,
 *  e.g. for Obj-no-split (MVars)
 *)
let counter = ref 0
let pv_counter = ref 0

let new_parameter_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (string ^ string_of_int !counter))

let new_bvar_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (string ^ string_of_int !counter))

let new_patvar_name () =
  pv_counter:= !pv_counter + 1;
  Id.mk_name (Id.SomeString ("v" ^ string_of_int !pv_counter))


let reset_counter () =
  (counter := 0 ; pv_counter := 0)


let eta_expand (tH, tA) = 
  let rec eta (tA, s) tS = match (tA, s) with 
  | LF.Atom _, s -> LF.Root(Syntax.Loc.ghost, tH, tS)
  | LF.PiTyp ((LF.TypDecl (x, tB0 ), _ ), tB), s -> 
      let tM = eta (tB0, s) LF.Nil in 
      LF.Lam (Syntax.Loc.ghost, x, eta (tB, S.LF.dot1 s) (LF.App (tM , tS))) in
    eta (tA, Substitution.LF.id) LF.Nil
      

(* ****************************************************************************** *)
(* Coverage problem *)
type gctx = (Id.name * Comp.typ * Comp.wf_tag) list

let rec lookup cG x = match cG with
  | (y,tau, _) :: cG ->
      if x = y then tau
      else lookup cG x

type problem = {loc : Syntax.Loc.t;
                prag : Pragma.case_pragma;           (* indicates if %not appeared after ``case...of'' *)
                cD : LF.mctx;
		cG : gctx;
                branches : Comp.branch list;
                ctype : Comp.typ}         (* type and context of scrutinee *)


let trivial_meta_obj cD  (_loc, m0) mT = match m0, mT with
  | LF.CObj (LF.CtxVar _ ) , _ -> true
  | LF.ClObj (phat, LF.MObj tM ) ,  LF.ClTyp (LF.MTyp _tA, cPsi) ->
      (match tM with
	 | LF.Root (_, LF.MVar (LF.Offset u, s), LF.Nil ) ->
	     let (_, _tA', cPsi') = Whnf.mctxMDec cD u in
		Whnf.convSub s (Substitution.LF.id) && Whnf.convDCtx cPsi' cPsi
	 | _ -> false
      )
  | LF.ClObj (phat, LF.PObj tH )  ,  LF.ClTyp (LF.PTyp tA, cPsi) ->
      (match tH with
	 | LF.PVar (p, s)  ->
	     let (_, _tA', cPsi') = Whnf.mctxPDec cD p in
	     Whnf.convSub s (Substitution.LF.id) && Whnf.convDCtx cPsi' cPsi
	 | _ -> false
      )

  | LF.ClObj (phat, LF.SObj s )  ,  LF.ClTyp (LF.STyp (_, cPhi), cPsi) ->
      ( match s with
	  | LF.SVar (0,0, s) -> Whnf.convSub s Substitution.LF.id
	  | _ -> false
      )
  | _ -> false


let is_id cD t cD' =
  let l = Context.length cD in
  let rec id t cD0 = match t, cD0 with
  | LF.MShift n , _ ->  n = l
  | LF.MDot (LF.MV _ , t), LF.Dec (cD0, _ ) -> id t cD0
  | LF.MDot (LF.CObj (LF.CtxVar _ ), t), LF.Dec (cD0, _ ) -> id t cD0
  | LF.MDot ((LF.ClObj (_, _) as m0), t), LF.Dec (cD0, LF.Decl(_, tU, _ ))->
      let  m0' = (Syntax.Loc.ghost, m0) in
      let b = trivial_meta_obj cD m0' (Whnf.cnormMetaTyp (tU,t)) in
	(* if b then () else print_string ("NON-Trivial Obj\n" ^ P.metaObjToString cD m0' ^ " \n");*)
	id t cD0 && b
  | _ -> false
  in
   id t cD'



let trivial_branch cD b tau_sc = match b, tau_sc  with
  | Comp.Branch (_loc, cD0, _cG, Comp.PatVar _ , t, _e), _  -> is_id cD0 t cD
  | Comp.Branch (_loc, cD0, _cG, Comp.PatMetaObj (_ , m0), t, _e), Comp.TypBox (_, mT) ->
      let b = trivial_meta_obj cD0 m0 (Whnf.cnormMetaTyp (mT, t)) in
	((* print_string ("Trivial Branch " ^ P.metaObjToString cD0 m0 ^ " ?\n");
	if b then print_string ("===> Yes\n") else print_string ("===> No\n");*)
	is_id cD0 t cD && b)
  | Comp.Branch (_loc, cD0, _cG, patt , _t, _e), _ -> false
  | _ -> false


let trivial_coverage cD branches tau_sc =
   List.exists (fun b -> trivial_branch cD b tau_sc) branches


(* Make a coverage problem *)
let make loc prag cD branches typ =
      {loc= loc;
       prag= prag;
       cD= cD;
       cG= [];
       branches= branches;
       ctype = typ }


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
		 | CovCtx of LF.dctx
		 | CovSub of  LF.dctx * LF.sub * LF.cltyp 
		 | CovPatt of gctx * Comp.pattern * Comp.tclo

type pattern =
  | MetaPatt  of  LF.dctx * LF.normal * LF.tclo
  | MetaCtx   of LF.dctx
  | MetaSub   of  LF.dctx * LF.sub * LF.cltyp
  | EmptyPatt of  LF.dctx * LF.tclo
  | EmptyParamPatt of  LF.dctx * LF.tclo
  | EmptyCompPatt of Comp.tclo
  | GenPatt of Comp.gctx * Comp.pattern * Comp.tclo


type eqn   = Eqn of cov_goal * pattern | EqnCtx of LF.dctx * LF.dctx 


type split = Split of cov_goal * pattern | SplitCtx of LF.dctx * LF.dctx
	     | SplitPat of (Comp.pattern * Comp.tclo)  * (Comp.pattern * Comp.tclo)

type candidate =
    Cand of  LF.mctx *  Comp.gctx *        (* meta-context of pattern        *)
              eqn list * split list

type candidates = candidate list

type covproblem = LF.mctx * gctx * candidates * Comp.pattern

type covproblems = covproblem list

let open_cov_goals  = ref ([]   :  (LF.mctx * gctx * Comp.pattern) list )

let reset_cov_problem () = open_cov_goals := []

type solved = Solved | NotSolvable | PossSolvable of candidate

type refinement_candidate =
  | TermCandidate of (LF.mctx * cov_goal * LF.msub)
  | CtxCandidate of (LF.mctx * LF.dctx * LF.msub)

(*  | PatCandidate of (LF.mctx * gctx * cov_goal * LF.msub * Comp.pattern list) *)

type refinement_cands =
    NoCandidate
  | SomeTermCands of depend * (refinement_candidate list)
  | SomeCtxCands of refinement_candidate list
(*  | SomePatCands of refinement_candidate list *)


let rec lower cPsi sA = match sA with
  | (LF.Atom (_ , a, _tS), s) -> (cPsi , Whnf.whnfTyp sA)
  | (LF.PiTyp ((decl, _ ), tB), s) -> lower (LF.DDec (cPsi, S.LF.decSub decl s)) (tB, S.LF.dot1 s)


let gen_str cD cPsi (LF.Atom (_, a, _tS) as tP) =
  let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
  let s_proj            = ConvSigma.gen_conv_sub conv_list in
  let s_tup             = ConvSigma.gen_conv_sub' conv_list in
    (*  cPsi |- s_proj : cPhi
        cPhi |- s_tup : cPsi       
        cPhi |- tQ   where  cPsi |- tP  !! tQ = [s_tup]tP !!  *)
  let tQ = Whnf.normTyp (tP, s_tup) in 
  let (ss', cPhi') = Subord.thin' cD a cPhi in
    (* cPhi |- ss' : cPhi' *)
  let ssi' = S.LF.invert ss' in
    (* cPhi' |- ssi : cPhi *)
    (* cPhi' |- [ssi]tQ    *)
    (* cPhi |- ss'    : cPhi'
       cPsi |- s_proj : cPhi
       cPsi |- comp  ss' s_proj   : cPhi' *)
  let ss_proj = S.LF.comp ss' s_proj in
     (ss_proj , (cPhi', LF.TClo(tQ,ssi')))



(* etaExpandMVstr cPsi sA  = tN
 *
 *  cPsi   |- [s]A <= typ
 *  cPsi   |- ss  <= cPsi'
 *  cPsi'  |- tN   <= [s'][s]A
 *)


let rec etaExpandMVstr cD cPsi sA  = etaExpandMVstr' cD cPsi (Whnf.whnfTyp sA)

and etaExpandMVstr' cD cPsi sA  = match sA with
  | (LF.Atom (_, a, _tS) as tP, s) ->
      let (cPhi, conv_list) = ConvSigma.flattenDCtx cD cPsi in
      let s_proj = ConvSigma.gen_conv_sub conv_list in
      let s_tup    = ConvSigma.gen_conv_sub' conv_list in
	(* let tQ    = ConvSigma.strans_typ cD cPsi (tP, s) conv_list in*)
      let tQ = Whnf.normTyp (tP, Substitution.LF.id) in  
       (* necessary to eliminate closures *)
      let tQ = Whnf.normTyp (tQ, Substitution.LF.comp s s_tup) in 
	(*  cPsi |- s_proj : cPhi
            cPhi |- s_tup : cPsi       
            cPhi |- tQ   where  cPsi |- tP  !! tQ = [s_tup]tP !!  *)

      let (ss', cPhi') = Subord.thin' cD a cPhi in
      (* cPhi |- ss' : cPhi' *)
      let ssi' = S.LF.invert ss' in
      (* cPhi' |- ssi : cPhi *)
      (* cPhi' |- [ssi]tQ    *)
      let u = Whnf.newMMVar None (cD, cPhi', LF.TClo(tQ,ssi')) LF.Maybe in
      (* cPhi |- ss'    : cPhi'
         cPsi |- s_proj : cPhi
         cPsi |- comp  ss' s_proj   : cPhi' *)
      let ss_proj = S.LF.comp ss' s_proj in
      let tM =  LF.Root (Syntax.Loc.ghost, LF.MMVar ((u,Whnf.m_id), ss_proj),  LF.Nil) in
	 tM

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

(* let rec mvlistToString mvlist = match mvlist with
  | [] -> ""
  | LF.Offset k :: []  -> string_of_int k
  | LF.Offset k :: mvl -> string_of_int k ^ " , " ^ mvlistToString mvl

*)
let rec gctxToCompgctx cG = match cG with
  | [] -> LF.Empty
  | (x,tau,flag) :: cG ->
      LF.Dec(gctxToCompgctx cG, Comp.CTypDecl (x, tau, flag))

let rec compgctxTogctx cG = match cG with
  | LF.Empty  -> []
  | LF.Dec(cG, Comp.CTypDecl (x,tau, flag)) ->
      (x,tau,flag)::compgctxTogctx cG


let pattToString cD patt = match patt with
  | MetaCtx cPsi ->       P.dctxToString cD cPsi 
  | MetaSub (cPsi, s, LF.STyp (_ , cPhi)) -> 
      P.dctxToString cD cPsi ^ " |- " ^ P.subToString cD cPsi s ^ " : "  ^ P.dctxToString cD cPhi
  | MetaPatt (cPsi, tR, sA) ->
      P.dctxToString cD cPsi ^ " |- " ^
      P.normalToString cD cPsi (tR, S.LF.id) ^ " : " ^ P.typToString cD cPsi sA
  | EmptyPatt (cPsi, sA) ->
           P.dctxToString cD cPsi ^ " |- " ^ "     ()    : " ^ P.typToString cD cPsi sA
  | EmptyParamPatt (cPsi, sA) ->
           P.dctxToString cD cPsi ^ " |- " ^ "     ()    : " ^ P.typToString cD cPsi sA


let covGoalToString cD cg = match cg with
  | CovCtx cPsi -> P.dctxToString cD cPsi
  | CovSub (cPsi, s, LF.STyp (_ , cPhi)) -> 
      P.dctxToString cD cPsi ^ " |- " ^ P.subToString cD cPsi s ^ " : "  ^ P.dctxToString cD cPhi
  | CovGoal(cPsi, tR, sA) ->
      P.dctxToString cD cPsi ^ " . " ^
	P.normalToString cD cPsi (tR, S.LF.id) ^ " : " ^ P.typToString cD cPsi sA
  | CovPatt (cG, patt, ttau) ->
      P.patternToString cD (gctxToCompgctx cG) patt ^ " : " ^ P.compTypToString cD (Whnf.cnormCTyp ttau)

let rec covGoalsToString cov_goals = match cov_goals with
  | [] -> "\n"
  | (cD, cg, _ ) :: cgoals ->
      " -- " ^  P.mctxToString cD ^ " |- " ^ covGoalToString cD cg ^
	"\n" ^  covGoalsToString  cgoals

let rec splitsToString' (cD, cG) (cD_p, cG_p) splits = match splits with
  | [] -> "\n"
  | (Split (cg, patt) :: splits ) ->
      covGoalToString cD cg ^ " == " ^ pattToString cD_p patt ^ "\n   "
      ^ splitsToString' (cD, cG) (cD_p, cG_p) splits
  | (SplitCtx (cPsi, cPhi) :: splits ) ->
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    "
      ^  splitsToString' (cD, cG) (cD_p, cG_p) splits
  | (SplitPat ((patt, ttau) , (patt', ttau')) :: splits ) ->
      P.patternToString cD cG patt ^ " : " ^ P.compTypToString cD (Whnf.cnormCTyp ttau) ^ " == " ^
	P.patternToString cD_p cG_p patt' ^ " : " ^
	P.compTypToString cD_p (Whnf.cnormCTyp ttau') ^ " , \n" ^
	splitsToString' (cD, cG) (cD_p, cG_p) splits
(*
let splitsToString (cD, cG) (cD_p, cG_p) splits =
  splitsToString' (cD, gctxToCompgctx cG) (cD_p, cG_p) splits
  *)
let rec eqnsToString cD cD_p eqns = match eqns with
  | [] -> "\n"
  | (Eqn (cg, patt) :: eqns ) ->
      covGoalToString cD cg ^ " == " ^ pattToString cD_p patt ^ "\n   "
      ^ eqnsToString cD cD_p eqns
(*  | (EqnCtx (cPsi, cPhi) :: splits ) ->
      P.dctxToString cD cPsi ^ " == " ^ P.dctxToString cD_p cPhi ^ "\n    "
      ^  eqnsToString cD cD_p splits
*)

let candToString (cD, cG) (Cand (cD_p, cG_p, eqns, splits)) =
	 P.mctxToString cD     ^ " ; \n"  ^
	 P.mctxToString cD_p ^ " \n   |- \n" ^
	 " MATCHES { \n    " ^ eqnsToString cD (cD_p) eqns ^ "         }\n" ^
	 " SPLITS { \n    " ^ splitsToString' (cD,cG) (cD_p, cG_p) splits ^ "          }\n]\n"

let rec candidatesToString' (cD, cG) candidates k = match candidates with
  | [] -> "\n\n"
  | (Cand (cD_p, cG_p, eqns, splits) :: cands) ->
       "[CANDIDATE " ^ string_of_int k ^ " : \n" ^
	 P.mctxToString cD     ^ " ; " ^ P.gctxToString cD cG ^ "\n"  ^
	 P.mctxToString cD_p ^ " ; " ^ P.gctxToString cD_p cG_p  ^ " \n   |- \n" ^
	 " MATCHES { \n    " ^ eqnsToString cD cD_p eqns ^ "         }\n" ^
	 " SPLITS { \n    " ^ splitsToString' (cD, cG) (cD_p, cG_p) splits ^ "          }\n]\n" ^
	 candidatesToString' (cD, cG)  cands (k+1)

let candidatesToString (cD,cG, candidates, patt ) =
  let cG' = gctxToCompgctx cG in
"\n##### COVERAGE GOAL : \n" ^
  "##### cD = " ^ P.mctxToString cD ^ 
"\n##### " ^ P.gctxToString cD cG' ^ " |- " ^
P.patternToString cD cG' patt
^ "\n##### is possibly covered by \n" ^
candidatesToString' (cD, cG') candidates 1
^ "\n###############################################"

let rec covproblemsToString cov_problems = match cov_problems with
  | [] -> "\n"
  | cov_prob :: cov_probs ->
      candidatesToString cov_prob ^ "\n   " ^ covproblemsToString cov_probs


let rec goalsToString ogoals k = match ogoals with
  | [] -> ""
  | (cD, cG, patt) :: ogoals ->
      "\n(" ^ string_of_int k ^ ")   " ^
        P.mctxToString cD ^ "\n " ^
	P.gctxToString cD (gctxToCompgctx cG) ^ "\n  |-  " ^
	P.patternToString cD (gctxToCompgctx cG) patt  ^ "\n" ^
	goalsToString ogoals (k+1)


let opengoalsToString ogoals = goalsToString ogoals 1

let opengoalToString (cD, cG, patt) = 
        P.mctxToString cD ^ "\n " ^
	P.gctxToString cD (gctxToCompgctx cG) ^ "\n  |-  " ^
	P.patternToString cD (gctxToCompgctx cG) patt  ^ "\n" 

(* ****************************************************************************** *)

type result = Yes of LF.tclo * LF.tclo | Inst | SplitCand | No 
(*    | CtxSplitCand of (eqn list * split list) *)

(* pre_match_head (cPsi, tH) (cPsi', tH') = result

- Yes (tA, tA') if tH is an instance of tH' and tH:tA and tH':tA'
- No            if tH can never be an instance of tH'
- Inst          if tH is claimed to be an instance of tH',
                  i.e. tH's structure matches the structure of a
                       subterm in tH', but there might be HO constraints
- SplitCand     if tH can maybe be an instance of tH' after we split
                tH further; this happens if tH is more general (i.e.
                it is a meta-variable or a parameter variable) than tH'


 *)
let rec pre_match_head cD cD' (cPsi, tH) (cPsi', tH') = match (tH , tH') with
(*  | (LF.MVar (LF.Offset u,s), LF.MVar (LF.Offset v,s')) ->
     if Whnf.convHead (tH, idSub) (tH', idSub) then
       let (_, tA, _cPsi)   = Whnf.mctxMDec cD u in
       Yes ((tA, s), (tA, s'))
     else
      Inst

   ** How to check that two terms M and N with mvars that fall outside
   the pattern fragment are identical? -
   **
   - Convertibility doesn't quite apply because cD and cD' might be different
   - Matching will fail due to unresolved constraints

*)
  | (_         , LF.MVar  _ ) -> Inst
  | (LF.BVar k , LF.BVar k') ->
      if k = k' then
	let LF.TypDecl (_x, tA )  = Context.ctxDec cPsi  k  in
	let LF.TypDecl (_y, tA') = Context.ctxDec cPsi' k' in
	  Yes ((tA,idSub), (tA', idSub))
      else No
  | (LF.PVar _ , LF.BVar k)  -> SplitCand
  | (LF.BVar k , LF.PVar _ ) -> Inst
(*
  | (LF.PVar (k,s) , LF.PVar (n,s')) ->
     if k = n then
       (match s, s' with
	| LF.Shift l, LF.Shift l' ->
	   if l = l' then
	     Inst (* could return Yes *)
	   else (if l < l' then SplitCand else No)
	| LF.Shift l, LF.EmptySub -> No
          (* this would mean the written pattern is not inhabited *)
	| _, _ -> Inst
       )
     else No
 *)
  | (LF.PVar (p,s), LF.PVar (q,s')) ->
    let ms = Ctxsub.mctxToMMSub cD cD' in
    let cPsi_p' = Whnf.cnormDCtx (cPsi', ms) in
    let tH'     = Whnf.cnormHead (tH', ms) in
    let mC, sC = pre_match_dctx cD cD' cPsi cPsi' [] [] in
      dprint (fun () -> ("[pre_match_head] pvar - case \n" ^
		 P.dctxToString cD  cPsi ^ " |- " ^ P.headToString cD cPsi tH ^ "\n" ^
		 P.dctxToString cD' cPsi' ^ " |- " ^ P.headToString cD' cPsi' tH' ^ "\n"));
       dprint (fun () -> ("pre_match_dctx yields  sC = " ^
		 splitsToString' (cD, LF.Empty) (cD', LF.Empty) sC ^
		 "                       mC = " ^
		 eqnsToString cD cD' mC ^ "\n")) ;
      begin try
	U.unifyDCtx cD cPsi cPsi_p' ;
	U.unifyH cD (Context.dctxToHat cPsi_p') tH tH';
	let (_, tA, _cPsi)   = Whnf.mctxPDec cD p in
	let (_, tA', _cPsi') = Whnf.mctxPDec cD' q in
	  Yes ((tA,idSub), (tA', idSub))
      with _ ->  dprint (fun () -> "[pre_match_head] pvar - SplitCand");
        SplitCand  (* CtxSplitCand (pre_match_dctx cD cD_p cPsi cPsi_p [] []) *)
      end
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

  | (LF.MVar _ ,  _         ) -> SplitCand

  | (LF.PVar _ , LF.Const _) -> No
  | (LF.Proj ( _, _ ) , LF.Const _ ) -> No
  | (LF.PVar _ , LF.Proj (LF.BVar _ , _ ) )-> No (* Inst *)
  | (LF.PVar _ , LF.Proj (LF.PVar _ , _ ) )-> No (* Inst *)
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
and pre_match cD cD_p covGoal patt matchCands splitCands =

  let CovGoal (cPsi, tM, sA ) = covGoal in
  let MetaPatt(cPhi, tN, sA') = patt in

  begin match  (tM, tN)  with
    | (LF.Lam (_ , x, tM) , LF.Lam (_, _y, tN)) ->

	let (LF.PiTyp((tdecl , _ ), tB ), s ) = Whnf.whnfTyp sA in
	let (LF.PiTyp((tdecl', _ ), tB'), s') = Whnf.whnfTyp sA' in

	let covGoal' = CovGoal (LF.DDec (cPsi, S.LF.decSub tdecl s),
				 tM, (tB, S.LF.dot1 s) ) in
	let patt'    = MetaPatt (LF.DDec (cPhi, S.LF.decSub tdecl' s'),
				 tN, (tB', S.LF.dot1 s')) in

	  pre_match cD cD_p covGoal' patt' matchCands splitCands

    | (LF.Root (_ , tH, tS), LF.Root (loc, tH', tS')) ->
	 begin match pre_match_head cD cD_p (cPsi, tH) (cPhi, tH') with
          | Yes (sA, sA') ->
	      pre_match_spine  cD cD_p
			       (cPsi , tS , sA)
			       (cPhi , tS', sA')
			       matchCands splitCands
          | No            -> raise (Error (loc,
						MatchError ("Head mismatch " ^ P.headToString cD cPsi tH ^ " =/= " ^ P.headToString cD_p cPhi tH' ^ "\n")))
	  | Inst          ->
	      (dprint (fun () -> "[pre_match] Eqn : " ^ 
			 covGoalToString cD covGoal ^ " == " ^ 
			 pattToString cD_p patt ^ "\n");
	      (Eqn (covGoal, patt) :: matchCands , splitCands))
	  | SplitCand     -> (matchCands , Split (covGoal, patt)::splitCands)
	  (* | CtxSplitCand (mC, sC) -> (mC @ matchCands , sC @ splitCands) *)
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
	let patt1     = MetaPatt (cPsi', tM', (tC1,s')) in

        let sB2' = (tB2, LF.Dot(LF.Obj(tM ), s)) in
        let sC2' = (tC2, LF.Dot(LF.Obj(tM'), s')) in

	let (matchCands', splitCands') = pre_match cD cD_p covGoal1 patt1 matchCands splitCands in

	  pre_match_spine cD cD_p (cPsi , tS , sB2')
                                    (cPsi', tS', sC2') matchCands' splitCands'
  end

and pre_match_sub cD cD_p covGoal patt  matchCands splitCands = 

  let CovSub (cPsi0,  s0, (LF.STyp (r0, cPhi0) as sT0)) = covGoal in
  let MetaSub (cPsi1, s1, (LF.STyp (r1, cPhi1) as sT1)) = patt in


  begin match (s0, cPhi0) , (s1, cPhi1) with 
    | (LF.EmptySub, LF.Null) , (LF.EmptySub, LF.Null) -> (matchCands, splitCands)
    | (LF.Shift k , _      ) , (LF.Shift n , _      ) -> 
	if n = k then (matchCands, splitCands)
	else 
	  raise (Error (Syntax.Loc.ghost,
			MatchError ("Substitution mismatch " ^ P.subToString cD cPsi0 s0 ^ " =/= " ^ P.subToString cD_p cPsi0 s1 ^ "\n")))

    | (LF.SVar(_, _, _), cPhi0) , (LF.Shift 0 , cPhi1) -> 
      (* SplitCand *)
      let covGoal = CovSub(cPsi0, s0, LF.STyp (r0, cPhi0)) in  
      let patt    = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in  
         (matchCands , Split (covGoal, patt)::splitCands)

      | (LF.Shift 0, cPhi0) , (LF.SVar( _ , _ , _), cPhi1) -> 
        let covGoal = CovSub(cPsi0, s0, sT0)   in  
        let patt    = MetaSub (cPsi1, s1, sT1) in 
         (Eqn (covGoal, patt)::matchCands, splitCands) 

      | (LF.SVar(_ , _ , _ ), _ ) , (LF.SVar(_ , _ , _), _ ) -> 
          let covGoal = CovSub(cPsi0, s0, LF.STyp (r0, cPhi0))   in  
          let patt    = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in 
            (Eqn (covGoal, patt)::matchCands, splitCands) 


      | (LF.Dot (f0, s0), LF.DDec(cPhi0, tdecl0)) , (LF.Dot (f1, s1), LF.DDec (cPhi1, tdecl1)) -> 
	  let LF.TypDecl (_, tA0) = tdecl0 in 
	  let LF.TypDecl (_, tA1) = tdecl1 in 
	  let covGoal = CovSub(cPsi0,  s0, LF.STyp (r0, cPhi0)) in 
	  let patt    = MetaSub (cPsi1, s1, LF.STyp (r1, cPhi1)) in 
	  let (matchCands', splitCands') = pre_match_front cD cD_p  (cPhi0, f0, tA0) (cPhi1, f1, tA1) matchCands splitCands in
            pre_match_sub cD cD_p covGoal patt matchCands'  splitCands' 

      | (LF.Shift n, _ ), (LF.Dot(LF.Head LF.BVar _k, _s'), _) ->
	  let s0 = LF.Dot (LF.Head (LF.BVar (n+1)), LF.Shift (n+1)) in 
	  let covGoal = CovSub(cPsi0, s0, LF.STyp (r0, cPhi0)) in 
            pre_match_sub cD cD_p covGoal patt matchCands splitCands

      | (LF.Dot(LF.Head LF.BVar _k, _s') , _ ) , (LF.Shift n, _ ) -> 
	  let s1   = LF.Dot (LF.Head (LF.BVar (n+1)), LF.Shift (n+1)) in 
	  let patt = MetaSub (cPsi1,  s1, LF.STyp (r1, cPhi1)) in 
            pre_match_sub cD cD_p covGoal patt matchCands splitCands


      | (LF.EmptySub, _ ) , ( _ , _ ) -> (matchCands, splitCands)
      | ( _ , _ ) , (LF.EmptySub, _ ) -> (matchCands, splitCands)


      | (LF.SVar _ , _ ), ( _  , _ ) ->  (matchCands , Split (covGoal, patt)::splitCands)

      | (_ , _ ) , (LF.SVar( _ , _ , _), _ ) -> (Eqn (covGoal, patt)::matchCands, splitCands) 


  end 

and pre_match_front cD cD_p (cPhi0, f0, tA0) (cPhi1, f1, tA1) matchCands splitCands = 
  begin match f0 , f1 with 
    | LF.Head h0, LF.Head h1 -> 
	let tM0     = eta_expand (h0, tA0) in 
	let tM1     = eta_expand (h1, tA1) in 
	let covGoal = CovGoal (cPhi0, tM0, (tA0, Substitution.LF.id)) in
	let patt    = MetaPatt(cPhi1, tM1, (tA1, Substitution.LF.id)) in
	  pre_match cD cD_p covGoal patt matchCands splitCands

    | LF.Obj tM0, LF.Obj tM1 -> 
	let covGoal = CovGoal (cPhi0, tM0, (tA0, Substitution.LF.id)) in
	let patt    = MetaPatt(cPhi1, tM1, (tA1, Substitution.LF.id)) in
	  pre_match cD cD_p covGoal patt matchCands splitCands
  end 



and pre_match_typ_spine cD cD_p (cPsi, tS1, sK1) (cPsi', tS2, sK2)
                       matchCands splitCands =
  begin match ((tS1,sK1), (tS2, sK2)) with
    | (LF.Nil, (LF.Typ, _ )) , (LF.Nil, (LF.Typ, _ )) -> (matchCands, splitCands)
    | (LF.App (tM, tS), sK) , (LF.App (tM', tS') , sK')->

	let (LF.PiKind((LF.TypDecl(_x, tB) , _ ), tK1 ), s)  = sK in
	let (LF.PiKind((LF.TypDecl(_y, tC) , _ ), tK2 ), s') = sK' in

	let covGoal1  = CovGoal  (cPsi , tM , (tB,s)) in
	let patt1     = MetaPatt (cPsi', tM', (tC,s')) in

        let sK1' = (tK1, LF.Dot(LF.Obj(tM ), s)) in
        let sK2' = (tK2, LF.Dot(LF.Obj(tM'), s')) in

	let (matchCands', splitCands') = pre_match cD cD_p covGoal1 patt1 matchCands splitCands in

	  pre_match_typ_spine cD cD_p (cPsi , tS , sK1')
                                        (cPsi', tS', sK2') matchCands' splitCands'
  end

and pre_match_typ cD cD_p (cPsi, sA) (cPhi, sB) matchCands splitCands =
  let _ = dprint (fun () ->
		    let cD' = cD_p in
		      "[pre_match_typ] sA = " ^ P.typToString cD cPsi sA ^ "\n" ^
		      "                sB = " ^ P.typToString cD' cPhi sB) in
    match (Whnf.whnfTyp sA , Whnf.whnfTyp sB) with
  | (LF.Atom (_, a, tS1) , s1) , (LF.Atom (loc, b, tS2), s2) ->
      let tK1 = (Types.get a).Types.kind in
      let tK2 = (Types.get b).Types.kind in
      let tS1' = Whnf.normSpine (tS1, s1) in
      let tS2' = Whnf.normSpine (tS2, s2) in
	if a = b then
	  pre_match_typ_spine cD cD_p (cPsi, tS1', (tK1, S.LF.id)) (cPhi, tS2', (tK2, S.LF.id))
                              matchCands splitCands
	else raise (Error (loc, MatchError "Type Head mismatch"))
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
  | (LF.SigmaLast(_, tA1), s1)  , (LF.SigmaLast (_, tA2), s2) ->
      pre_match_typ cD cD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands
  | (LF.SigmaElem (x1, tA1, trec1) , s1) , (LF.SigmaElem (x2, tA2, trec2) , s2) ->
      let (mC, sC) = pre_match_typ cD cD_p (cPsi , (tA1, s1)) (cPhi, (tA2, s2)) matchCands splitCands in
	pre_match_trec cD cD_p (LF.DDec(cPsi, LF.TypDecl(x1, LF.TClo(tA1,s1)))) (LF.DDec(cPhi, LF.TypDecl(x2, LF.TClo(tA2,s2))))
	  (trec1, S.LF.dot1 s1) (trec2, S.LF.dot1 s2)
	  mC sC


and pre_match_dctx cD cD_p cPsi cPhi_patt matchCands splitCands =
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


let match_metaobj cD cD_p ((loc,mO),mt) ((loc',mO_p),mtp) mC sC = match ((mO,mt), (mO_p,mtp)) with
  | (LF.CObj cPsi , _w) , (LF.CObj cPsi', _w') ->
      pre_match_dctx cD cD_p cPsi cPsi' mC sC
  | (LF.ClObj (_, LF.MObj tR), LF.ClTyp (LF.MTyp tA, cPsi)),
      (LF.ClObj (_ , LF.MObj tR') , LF.ClTyp (LF.MTyp tA', cPsi'))  ->
      let (mC0, sC0) = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
      let (mC1, sC1) = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
      let covGoal = CovGoal (cPsi, tR, (tA, S.LF.id)) in
      let pat = MetaPatt (cPsi', tR', (tA', S.LF.id)) in
	pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.MObj tR), LF.ClTyp (LF.PTyp tA, cPsi)),
      (LF.ClObj (_ , LF.MObj tR') , LF.ClTyp (LF.PTyp tA', cPsi'))  ->
      let (mC0, sC0)  = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
      let (mC1, sC1) = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
      let covGoal = CovGoal (cPsi, tR, (tA, S.LF.id)) in
      let pat = MetaPatt (cPsi', tR', (tA', S.LF.id)) in
	pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.PObj tH), LF.ClTyp (LF.PTyp tA, cPsi)),
      (LF.ClObj (_ , LF.PObj tH') , LF.ClTyp (LF.PTyp tA', cPsi'))  ->
      let (mC0, sC0) = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
      let (mC1, sC1) = pre_match_typ cD cD_p (cPsi, (tA, S.LF.id)) (cPsi', (tA', S.LF.id)) mC0 sC0 in
      let loc = Syntax.Loc.ghost in
      let covGoal = CovGoal (cPsi, LF.Root(loc, tH, LF.Nil), (tA, S.LF.id)) in
      let pat = MetaPatt (cPsi', LF.Root (loc, tH', LF.Nil), (tA', S.LF.id)) in
	pre_match cD cD_p covGoal pat mC1 sC1
  | (LF.ClObj (_, LF.SObj s), LF.ClTyp (sT, cPsi)),
      (LF.ClObj (_ , LF.SObj s') , LF.ClTyp (sT', cPsi'))  ->
      let (mC1, sC1) = pre_match_dctx cD cD_p cPsi cPsi' mC sC in
      let covGoal = CovSub (cPsi, s, sT) in
      let pat = MetaSub (cPsi', s', sT') in
	pre_match_sub cD cD_p covGoal pat mC1 sC1
    | (_ , _ ) -> raise (Error (Syntax.Loc.ghost, MatchError ("Meta Obj Mismatch \n" ^ "Found CovGoal: " ^ P.metaObjToString cD (loc, mO) ^ " : " ^ P.metaTypToString cD mt  ^ "\nPattern: " ^ P.metaObjToString cD_p (loc', mO_p) ^ " : " ^ P.metaTypToString cD_p mtp ^ "\n")))



let rec match_pattern (cD, cG) (cD_p, cG_p) (pat, ttau) (pat_p, ttau_p) mC sC =
match (pat, ttau) , (pat_p, ttau_p) with
  | (Comp.PatMetaObj (loc, mO) , (Comp.TypBox (_, mT), t)) ,
    (Comp.PatMetaObj (_loc, mO'), (Comp.TypBox (_, mT'), t')) ->
      let mT0  = Whnf.cnormMTyp (mT , t ) in 
      let mT0' = Whnf.cnormMTyp (mT', t') in 
      match_metaobj cD cD_p (mO, mT0) (mO', mT0') mC sC


  | (Comp.PatConst (_, c, pS) , (Comp.TypBase _, t)) ,
    (Comp.PatConst (loc, c', pS'), (Comp.TypBase _,t')) ->
      if c = c' then
	let ttau = ((Store.Cid.CompConst.get c).Store.Cid.CompConst.typ, Whnf.m_id) in
	let ttau' = ((Store.Cid.CompConst.get c').Store.Cid.CompConst.typ, Whnf.m_id) in
	match_spines (cD, cG) (cD_p, cG_p) (pS, ttau) (pS', ttau') mC sC
      else
	raise (Error (loc, MatchError "Const mismatch"))
  | (pat, ttau),
    (Comp.PatVar (_, v), ttau') ->   (* success *)
      (mC, sC)

  | (Comp.PatFVar (_, v) , ttau),
    (pat_p, ttau')  -> (* splitting candidate *)
      (mC, SplitPat ((pat, ttau) , (pat_p, ttau')) :: sC)

  | (Comp.PatPair (_, pat1, pat2) , (Comp.TypCross (tau1, tau2), t)),
    (Comp.PatPair (_, pat1', pat2'), (Comp.TypCross (tau1', tau2'),t')) ->
      let (mC1, sC1) = match_pattern (cD,cG) (cD_p, cG_p)
	                 (pat1, (tau1,t)) (pat1', (tau1',t')) mC sC in
	match_pattern (cD,cG) (cD_p, cG_p)
	  (pat2, (tau2,t))  (pat2', (tau2',t')) mC1 sC1
  | (Comp.PatTrue _ , _ ),
    (Comp.PatTrue _ , _ ) -> (mC, sC)
  | (Comp.PatFalse _ , _ ),
    (Comp.PatFalse _ , _ ) -> (mC, sC)
  | pat_ttau , (Comp.PatAnn (_, pat', tau' ), (_ ,t'))  ->
      match_pattern (cD,cG) (cD_p, cG_p) pat_ttau (pat', (tau',t')) mC sC
  | (Comp.PatAnn (_, pat', tau' ), (_ ,t')), pat_ttau  ->
      match_pattern (cD,cG) (cD_p, cG_p) (pat', (tau',t')) pat_ttau mC sC
  | _ -> raise (Error (Syntax.Loc.ghost, MatchError "Mismatch"))

and match_spines (cD,cG) (cD_p, cG_p) pS pS' mC sC = match (pS, pS') with
  | (Comp.PatNil , _ ) ,
    (Comp.PatNil , _ ) -> (mC, sC)
  | (Comp.PatApp (_ , pat, pS) , (Comp.TypArr (tau1, tau2) , t)) ,
    (Comp.PatApp (_, pat', pS') , (Comp.TypArr (tau1', tau2'),t')) ->
     let (mC1, sC1) = match_pattern (cD,cG) (cD_p, cG_p)
                         (pat, (tau1,t)) (pat', (tau1',t')) mC sC in
	match_spines (cD,cG) (cD_p, cG_p)
	  (pS, (tau2,t)) (pS', (tau2',t')) mC1 sC1
  | (Comp.PatApp (_ , pat, pS) , (Comp.TypPiBox ((LF.Decl (_, LF.ClTyp (LF.MTyp tA, cPsi), _)), tau2), t)),
    (Comp.PatApp (_, pat', pS') , (Comp.TypPiBox ((LF.Decl (_, LF.ClTyp (LF.MTyp tA', cPsi'), _)), tau2'), t')) ->
      let Comp.PatMetaObj (_, (loc,mO)) = pat in
      let Comp.PatMetaObj (_, (loc',mO')) = pat' in
      let tau1 = LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA,t)), Whnf.cnormDCtx (cPsi, t)) in
      let tau1' = LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA',t')), Whnf.cnormDCtx (cPsi', t')) in

      let t2 = LF.MDot(mO, t) in
      let t2' = LF.MDot(mO', t') in
      let (mC1, sC1) = match_metaobj cD cD_p ((loc,mO), tau1) ((loc',mO'), tau1') mC sC in
	match_spines (cD,cG) (cD_p, cG_p)
	  (pS, (tau2, t2)) (pS', (tau2', t2')) mC1 sC1

  | (Comp.PatApp (_ , pat, pS) , (Comp.TypPiBox ((LF.Decl(_x,LF.CTyp w, _ )), tau2), t)),
    (Comp.PatApp (_, pat', pS') , (Comp.TypPiBox ((LF.Decl(_,LF.CTyp w',_ )) , tau2'), t')) ->
      let Comp.PatMetaObj (_, (loc,mO)) = pat in
      let Comp.PatMetaObj (_, (loc',mO')) = pat' in
      let tau1 = LF.CTyp w in
      let tau1' = LF.CTyp w' in
      let t2 = LF.MDot(mO, t) in
      let t2' = LF.MDot(mO', t')in
      let (mC1, sC1) = match_metaobj cD cD_p ((loc,mO), tau1) ((loc',mO'), tau1') mC sC in
	match_spines (cD,cG) (cD_p, cG_p)
	  (pS, (tau2, t2)) (pS', (tau2', t2')) mC1 sC1

  |  _ , (Comp.PatApp (loc, _pat', _pS') , _ )
        -> raise (Error (loc, MatchError "Spine Mismatch"))

  | _ -> raise (Error (Syntax.Loc.ghost, MatchError "Spine Mismatch"))

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
      let tN = etaExpandMVstr cD cPsi (tA, s)  in
      let tS  = genSpine cD cPsi (tB, LF.Dot(LF.Obj(tN), s))  tP  in
	LF.App (tN, tS)

  | (LF.Atom (_ , _a, _tS) as tQ, s) ->
      (U.unifyTyp LF.Empty cPsi (tQ, s) (tP, idSub);
       LF.Nil )
end


(* genObj (cD, cPsi, tP) (tH, tA) =  (cD', CovGoal (cPsi', tR, tP'), ms)

   if cD ; cPsi |- tH => tA   and
      there exists a spine tS s.t.  cD ; cPsi |- tS : A > P
   then

      R = Root (tH, tS) and cD' ; [ms]cPsi |- tR <= [ms]tP
                        and cD' |- ms : cD

*)
let genObj (cD, cPsi, tP) (tH, tA) =
    (* make a fresh copy of tP[cPsi] *)
(* !! bp    let _ = dprint (fun () -> "[genObj] cD = " ^ P.mctxToString cD) in *)
    let ms    = Ctxsub.mctxToMSub cD in
(*    let _ = dprint (fun () -> " ms = " ^ P.msubToString LF.Empty ms ) in *)
    let tP'   = Whnf.cnormTyp (tP, ms) in
    let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
    let tA'   = Whnf.cnormTyp (Whnf.normTyp (tA, S.LF.id), ms) in
    let tH'   = Whnf.cnormHead (tH, ms) in
(* !! bp    let _ = dprint (fun () -> "[genObj] Head of type : " ^
		      P.dctxToString LF.Empty cPsi' ^ " |- " ^
		      P.typToString LF.Empty cPsi' (tA', S.LF.id) )      in
*)
    let tM = LF.Root (Syntax.Loc.ghost, tH' , genSpine LF.Empty cPsi' (tA', S.LF.id) tP') in
    let _ = dprint (fun () -> "[genObj] Generated Head : " ^ P.headToString cD cPsi tH) in
    let _ = dprint (fun () -> "[genObj] type of head : " ^ P.typToString cD cPsi (tA, S.LF.id) ^ " as suitable head ") in
    let _ = dprint (fun () -> "[genObj] for " ^ P.dctxToString cD cPsi ^ " |- " ^ P.typToString cD cPsi (tP, S.LF.id)) in

    let _  = U.forceGlobalCnstr (!U.globalCnstrs) in
    let (cD', cPsi', tR, tP', ms') =
      begin try
	Abstract.covgoal cPsi'  tM   tP' (Whnf.cnormMSub ms) (* cD0 ; cPsi0 |- tM : tP0 *)
      with Abstract.Error (_, Abstract.LeftoverConstraints) as e ->
	(print_string ("WARNING: Encountered left-over constraints in higher-order unification\n");
	 print_string ("Coverage goal : " ^ P.normalToString LF.Empty  cPsi' (tM, S.LF.id) ^ " : " ^
			  P.typToString LF.Empty cPsi' (tP', S.LF.id) ^ "\n");
	 raise e)
      end
      in
    let (cPsi', tR', tP')  = (Whnf.normDCtx cPsi', Whnf.norm (tR, S.LF.id), Whnf.normTyp (tP', S.LF.id)) in
      (cD' , CovGoal (cPsi', tR', (tP', S.LF.id)), ms')

let rec genAllObj cg tHtA_list  = match tHtA_list with
  | [] -> []
  | tH_tA :: tHAlist ->
      let cgs = genAllObj cg tHAlist in 
      begin try
       (genObj cg tH_tA)::cgs	   
      with U.Failure _msg -> cgs
	| U.GlobalCnstrFailure (_, _msg) -> cgs
(*	| _ ->(dprint (fun () -> "Other failure - no Obj generated") ;genAllObj cg tHAlist)*)
      end

let genConst  ((cD, cPsi, LF.Atom (_, a, _tS)) as cg) =
  begin
    let _ = Types.freeze a in
    let constructors = (Types.get a).Types.constructors in
      (* Reverse the list so coverage will be checked in the order that the
	 constructors were declared, which is more natural to the user *)
    let constructors = List.rev !constructors in
    let tH_tA_list   = List.map (function c -> (LF.Const c,
						(Const.get  c).Const.typ))
                                constructors
    in
      genAllObj cg tH_tA_list
  end


let genHeads (tH, tA) = begin match Whnf.whnfTyp (tA, S.LF.id) with
  | (LF.Sigma tArec, s) ->
      let k = LF.blockLength tArec in
      let rec getComponents i = if i = k+1 then []
      else
	(LF.Proj (tH, i) , LF.TClo (LF.getType tH (tArec, s) i 1)) :: getComponents (i+1)
      in
	getComponents 1
  | _ -> [(tH, tA)]
end

let genBVar ((_cD, cPsi, _tP) as cg) =
  let k = Context.dctxLength cPsi in

  let rec genBVarCovGoals i  = if i = (k+1) then []
   else
    let LF.TypDecl (_ , tA)  = Context.ctxDec cPsi i in   (* x_i : tA   in   cPsi *)
    let tH_tA_list   = genHeads (LF.BVar i , tA) in
    let cov_goals_i  = genAllObj  cg tH_tA_list in
      cov_goals_i @ genBVarCovGoals (i+1)
  in
    genBVarCovGoals 1


let genPVar (cD, cPsi, tP)   =
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
	  | ((LF.SchElem (decls, trec) as _scelem) :: elems) ->
	      let pv_list = genPVarCovGoals elems in
	      (* let _ = dprint (fun () -> "[genPVar] for schema element: " ^ P.schElemToString scelem) in *)
	      let cPhi             = Context.projectCtxIntoDctx decls in
	      let (cD', s, offset) = Ctxsub.ctxToSub_mclosed cD  cvar_psi cPhi in
		(* cO ; cD' ; psi |- [s]trec  *)
		(* cO ; cD'  |- (cPsi, mshift offset)
		   cO ; cD' ; (cPsi, mshift offset) |- (tP, mshift offset)
		*)
	      let trec'     = Whnf.normTypRec (trec, s) in

	      let (pdecl, tA)  = (match trec' with
				      LF.SigmaLast(n, tA) ->
					(LF.Decl(new_parameter_name "p",
						   LF.ClTyp (LF.PTyp tA, Whnf.cnormDCtx (cvar_psi, LF.MShift offset)), LF.Maybe) , tA)
				    | LF.SigmaElem _  ->
					(LF.Decl (new_parameter_name "p",
						    LF.ClTyp (LF.PTyp (LF.Sigma trec'), Whnf.cnormDCtx (cvar_psi, LF.MShift offset)), LF.Maybe) , LF.Sigma trec')
			   ) in

	      let cD'_pdecl = LF.Dec(cD', pdecl) in
	      let cPsi'  = Whnf.cnormDCtx (cPsi, LF.MShift (offset + 1)) in
	      let tP'    = Whnf.cnormTyp (tP, LF.MShift (offset + 1)) in
	      let cg'    = (cD'_pdecl, cPsi', tP') in

	      let id_psi = Substitution.LF.justCtxVar cPsi' in
		(* cO ; cD_ext, pdec   ; cPsi' |- id_psi : cvar_psi  *)

	      let h      = LF.PVar (1, id_psi) in
	      let tA' = Whnf.normTyp (Whnf.cnormTyp (tA, LF.MShift 1), id_psi) in
		(* cO ; cD', pdec ; cPsi'  |- p[id_psi] : [id_psi](trec[|MShift 1|])
		   or to put it differently
		   cO ; cD', pdec ; cPsi'  |- head : trec'
		*)
	      let tH_tA_list = genHeads (h, tA') in
	      let _ = dprint (fun () -> "#Generated Heads = " ^ string_of_int (List.length tH_tA_list)) in
	      let cg_list    = genAllObj cg' (tH_tA_list) in
	      let _ = dprint (fun () -> "#Generated Obj = " ^ string_of_int (List.length cg_list)) in
              (* each cg in cg_list:    (cO_k,cD_k), ms_k
                 where cD_k |- ms_k : cD'_pdcl
                 we need however:    cD_k |- ms'_k : cD

                    mcomp (MShift (offset + 1) ms_k
               *)
	      let cg_list'    = List.map (fun (cD',cg, ms) ->
					    (cD', cg, Whnf.mcomp (LF.MShift (offset + 1)) ms)) cg_list in
	      let all_cg = cg_list' @ pv_list in
	      (* let _ = dprint (fun () -> "Generated " ^ string_of_int (List.length all_cg) ^ " pvar cases") in
	         let _ = dprint (fun () -> "They are: " ^ covGoalsToString all_cg) in
	      *)
		all_cg   
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


(* genCovGoals (cD, cPsi, tA) = S

   if cD ; cPsi |- tA  (the type we need to cover, i.e. the coverage problem)

   then S is a list of meta-context cD_i, cg_i = CovGoal (cPsi_i, tR_i, tP_i)
                   and refinement substitutions ms_i s.t.

       S = { (cD_i, cg_i, ms_i) |

              cD_i |- ms_i : cD
              cD_i ; cPsi_i |- tR_i : tP_i
           }
*)
let rec genCovGoals (((cD, cPsi, tA) as cov_problem) : (LF.mctx * LF.dctx * LF.typ) )
 =  match tA  with
  | LF.Atom _ ->
      let g_pv = genPVar cov_problem in (* (cD', cg, ms) list *)
      (* let _ = dprint (fun () -> "[genCovGoals] generated pvar cases\n") in *)
      let g_bv = genBVar cov_problem in
      (* let _ = dprint (fun () -> "[genCovGoals] generated bvar cases\n") in *)
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



let rec solve' cD (matchCand, ms) cD_p mCands' sCands' = match matchCand with
  | [] -> (match sCands' with
             | []  ->  begin try ((* dprint (fun () -> "[solve'] Check that all global constraints are true");*)
                                  U.forceGlobalCnstr (!U.globalCnstrs);
                                  dprint (fun () -> "[solve'] All global constraints are true.");
                                  Solved)
                      with
                        | U.Failure "Unresolved constraints" ->
                          (dprint (fun () -> "Global constraints failed\n");
                         (* PossSolvable (Cand (cD_p , LF.Empty, mCands, sCands)) *)
                           NotSolvable
                          )
                        | U.GlobalCnstrFailure (_ , cnstr) ->
 	                 (* let _ = print_string ("Unification of global constraint " ^ cnstr ^ " failed.\n")
                         in *)
                         NotSolvable
                      end
	     | _ -> PossSolvable (Cand (cD_p , LF.Empty, mCands', sCands')))
  | mc :: mCands ->
      begin match mc with
	| Eqn (CovSub (cPsi, s, sT), MetaSub (cPsi_p, s_p, sT_p) ) -> 
	    let cT      = LF.ClTyp (sT, cPsi) in 
	    let cT_p    = LF.ClTyp (sT_p, cPsi_p) in 
	    let cM      = (Syntax.Loc.ghost, LF.ClObj (Context.dctxToHat cPsi , LF.SObj s)) in 
	    let cM_p    = (Syntax.Loc.ghost, LF.ClObj (Context.dctxToHat cPsi_p, LF.SObj s_p)) in 
	      begin try
		U.unifyMetaTyp cD (cT, Whnf.m_id) (cT_p, ms);
		U.unifyMetaObj cD (cM, Whnf.m_id) (cM_p,ms) (cT, Whnf.m_id);
		solve' cD (mCands, ms) cD_p (mc::mCands') sCands'
	      with 
              | U.GlobalCnstrFailure ( _loc, cnstr) -> NotSolvable
	      | U.Failure msg  ->
		  (if U.unresolvedGlobalCnstrs () then
		     let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND") in
		     let sc = Split (CovSub (cPsi, s, sT) , MetaSub (cPsi_p, s_p, sT_p)) in
		       solve' cD (mCands, ms) cD_p mCands' (sc::sCands')
		   else
                     begin match msg with
                       | "Pruning" ->
			   (* Match Candidate is kept ? *)
			   let sc = Split (CovSub (cPsi, s, sT) , MetaSub (cPsi_p, s_p, sT_p)) in
			     solve' cD (mCands, ms) cD_p (mCands') (sc::sCands')
                       | _ ->
			   (* we are not trying to be clever and see if a context split would lead to progress *)
			   let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ " \n NOT SOLVABLE\n") in
			     NotSolvable
	             end)
	      end

	| Eqn (CovGoal (cPsi, tR, sA) , MetaPatt (cPsi_p, tR_p, sA_p)) ->
	  let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in
	  let tR_p'   = Whnf.cnorm (tR_p, ms) in
	  let tA_p'   = Whnf.cnormTyp (Whnf.normTyp sA_p,  ms) in
	  let _       = (dprint (fun () -> "\n[solve'] " ^ P.dctxToString cD  cPsi ^
				   "    ==    " ^ P.dctxToString cD cPsi_p' );
			 dprint (fun () -> "        " ^ P.typToString cD cPsi sA ^
				   "    ==    " ^ P.typToString cD cPsi (tA_p', S.LF.id)) ;
			 dprint (fun () -> "        " ^
				   P.normalToString cD cPsi (tR, S.LF.id) ^
				   "    ==    " ^ P.normalToString cD cPsi (tR_p', S.LF.id) ^ "\n")) in

	    begin try
	      U.unifyDCtx cD cPsi cPsi_p' ;
	      U.matchTyp cD cPsi sA (tA_p', S.LF.id);
	      U.matchTerm cD cPsi (tR, S.LF.id) (tR_p', S.LF.id) ;
	      solve' cD (mCands, ms) cD_p (mc::mCands') sCands'
	    with
	      (* should this case betaken care of  during pre_match phase ? *)
              | U.GlobalCnstrFailure ( _loc, cnstr) ->
		 let _ = print_string ("Unification of pre-solved equation failed due to the fact the constraint " ^ cnstr ^ " cannot be solved.") in
                   NotSolvable
	      | U.Failure "Context clash" ->
		 let _ = print_string "Unification of pre-solved equation failed due to context mismatch - initiate context matching" in
	      	let sc = SplitCtx (cPsi , cPsi_p) in
		let _ = dprint (fun () -> "Initiate context splitting: " ^ P.dctxToString cD cPsi ^ " == " ^
		  P.dctxToString cD cPsi_p' ^ " \n") in
		  solve' cD (mCands, ms) cD_p mCands' (sc::sCands')
	      | U.Failure msg ->
	      (if U.unresolvedGlobalCnstrs () then
		let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ "\n MOVED BACK TO SPLIT CAND") in
		let sc = Split (CovGoal (cPsi, tR, sA) , MetaPatt (cPsi_p, tR_p, sA_p)) in
		  solve' cD (mCands, ms) cD_p mCands' (sc::sCands')
	      else
                begin match msg with
                  | "Pruning" ->
                    (* Match Candidate is kept ? *)
		    let sc = Split (CovGoal (cPsi, tR, sA) , MetaPatt (cPsi_p, tR_p, sA_p)) in
                      solve' cD (mCands, ms) cD_p (mCands') (sc::sCands')
                  | _ ->
		    let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ^ " \n NOT SOLVABLE\n") in
                     NotSolvable
	        end)
            end

	| EqnCtx (cPsi, cPsi_p) ->
	    let cPsi_p' = Whnf.cnormDCtx (cPsi_p, ms) in
	      begin try
		dprint (fun () -> "EqnCtx " ^ P.dctxToString cD cPsi ^ " == " ^
			  P.dctxToString cD cPsi_p' ^ " \n");
		U.unifyDCtx cD cPsi cPsi_p' ;
		solve' cD (mCands, ms) cD_p (mc::mCands') sCands'
	      with U.Failure msg ->
		  let _ = dprint (fun () -> " UNIFY FAILURE " ^ msg ) in
		    NotSolvable
	      end
      end


let solve cD cD_p matchCand = match matchCand with
  | [] ->  Solved

  | mc :: mCands ->
      let ms = Ctxsub.mctxToMMSub cD cD_p in
	solve' cD (matchCand ,  ms) cD_p [] []

(* refineSplits cD cD_p matchL splitL ms = (matchL', splitL')

 if   cD |- matchL
      cD |- ms : cD0
      cD0  |- splitL
then
      cD |- matchL'    and matchL @ matchL0 = matchL'
      cD |- splitL'    and splitL' is the refined splitL
*)
let rec refineSplits (cD:LF.mctx) (cD_p:LF.mctx) matchL splitL ms = match splitL with
  | [] -> (matchL , [] )
  | Split (CovGoal (cPsi, tR, sA) , patt ) :: splits ->
      (let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in
      let tA     = Whnf.normTyp sA in

      let (cPsi, tR, tA) = (Whnf.cnormDCtx (cPsi, ms), Whnf.cnorm (tR, ms), Whnf.cnormTyp (tA, ms)) in

      let (CovGoal (cPsi', tR', sA')  as covG)   = CovGoal (cPsi, tR, (tA, S.LF.id))  in
      (* let MetaPatt(cPhi, _tN, sB') = patt in *)
      (* let (mL', sL') = pre_match_typ cD cD_p (cPsi, sA') (cPhi, sB') matchL' splitL' in   *)
      (* let (mL', sL') = pre_match_dctx cD cD_p cPsi cPhi matchL' splitL' in *)
      let result = pre_match cD cD_p covG patt matchL' splitL' in
	result
      )
  | Split (CovSub (cPhi, s, sT) , patt ) :: splits ->
      let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in
       let covG = CovSub (Whnf.cnormDCtx (cPhi, ms), Whnf.cnormSub (s, ms), Whnf.cnormClTyp (sT, ms)) in 
	 pre_match_sub cD cD_p covG patt matchL' splitL'
      
  | SplitCtx (cPsi, cPsi_patt ) :: splits ->
      let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in
      let cPsi' = Whnf.cnormDCtx (cPsi, ms) in
	pre_match_dctx cD  cD_p cPsi' cPsi_patt matchL' splitL'

  | SplitPat ((Comp.PatFVar (loc, x) , (tau,t)) , pPatt_p) :: splits ->
      let (matchL', splitL') = refineSplits cD cD_p matchL splits ms in
      	(matchL', SplitPat ((Comp.PatFVar (loc, x), (tau, Whnf.mcomp t ms)), pPatt_p )::splitL')

(* cnormCtx (cG, ms) = cG' *)
let rec cnormCtx (cG, ms) = match cG with
  | [] -> []
  | (x,tau, flag) :: cG' -> (x, Whnf.cnormCTyp (tau, ms),flag) :: (cnormCtx (cG', ms))

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

(* refine_cand (cD', cG', ms) (cD, cG, cand) = [ms]cand

if
   cD' |- ms : cD
   cD ; cG |- cand
then
   cD' ; cG' |- [ms]cand

*)

let refine_cand (cD',cG', ms) (cD, cG, Cand (cD_p, cG_p, matchL, splitL)) =
  let matchL' = cnormEqn matchL  ms in
  let _ = dprint (fun () -> "[refine_cand] cD' = " ^ P.mctxToString cD') in
  let (matchL0,splitL0) = refineSplits cD' cD_p matchL' splitL ms in
  (* let _ = dprint (fun () -> "[refine_cand] splitL = " ^ splitsToString (cD, cG) (cD_p, cG_p) splitL) in
  let _ = dprint (fun () -> "[refine_cand] splitL' = " ^ splitsToString (cD', cG') (cD_p, cG_p) splitL0) in *)
    Cand (cD_p, cG_p, matchL0, splitL0)

let rec refine_candidates (cD', cG', ms) (cD, cG, candidates) = match candidates with
  | [] -> []
  | cand :: cands ->
      begin try
        let _ = dprint (fun () -> "[refine_candidates] REFINING candidate : " ^
			  candToString (cD, LF.Empty) cand  ) in
	let cand' = refine_cand (cD', cG', ms) (cD, cG, cand)  in
	let _ = dprint (fun () -> "REFINED CANDIDATE \n" ^ candToString (cD', LF.Empty) cand')  in
	  cand' :: refine_candidates (cD', cG', ms) (cD, cG, cands)
      with
	  Error (_, MatchError _) ->
            (dprint (fun () -> "[refine_candidate] not relevant candidate : " ^
              candToString (cD, LF.Empty) cand  );
            refine_candidates (cD', cG', ms) (cD, cG, cands))
      end


let rec refine_pattern cov_goals ( (cD, cG, candidates, patt ) as cov_problem ) =
  match cov_goals with
  | [] -> []
  | (TermCandidate ((cD_cg, _, ms) as cg)) :: cgs  ->
       let _ = dprint (fun () -> "\n##### [Consider coverage goal] \n     " ^ covGoalsToString [cg] ) in
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^
			  " candidates.\n");
                (* dprint (fun () -> "Are candidates covering? - \n       " ^ candidatesToString (cD,cG, candidates, patt));*)
		(* dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms )*))   in

       let cG'         = cnormCtx (cG, ms) in
       let candidates' = refine_candidates (cD_cg, cG', ms) (cD, cG, candidates) in

       let _ =  dprint (fun () -> "[refine_candidates] DONE : The remaining #refined candidates = " ^ string_of_int  (List.length candidates')) in

       let pat' = Whnf.cnormPattern (patt, ms) in

	 (match candidates' with
	   | [] -> (dprint (fun () -> "[OPEN COVERAGE GOAL] " ^ covGoalsToString [cg] ) ;
	            open_cov_goals := (cD_cg, cG', pat')::!open_cov_goals ;
		    refine_pattern cgs cov_problem )
	   | _  ->
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates'));
	       dprint (fun () -> "  Covering Candidates (after refine_pattern) : \n         " ^
                 candidatesToString (cD_cg, cG', candidates', pat')) ;
	       ((cD_cg, cG', candidates', pat') :: refine_pattern cgs cov_problem) )
	 )

  | CtxCandidate (cD_cg, cPhi_r, ms) :: cgs  ->
       let _ = dprint (fun () -> "\n##### [Consider context goal] \n     " ^
			 P.dctxToString cD_cg cPhi_r) in
       let _ = (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates) ^
			  " candidates.\n");
		dprint (fun () -> "cD = " ^ P.mctxToString cD);
		dprint (fun () -> "ms = " ^ P.msubToString cD_cg ms ))   in

	 let cG'     = cnormCtx (cG, ms) in
       let candidates' = refine_candidates (cD_cg, cG', ms) (cD, cG, candidates) in

       let _ =  dprint (fun () -> "[refine_candidates] DONE : " ^
                            "Remaining #refined candidates = " ^
			  string_of_int (List.length candidates')) in
       let pat' = Whnf.cnormPattern (patt, ms) in
	 let _ = dprint (fun () -> "cG = " ^ P.gctxToString cD (gctxToCompgctx cG)) in
	 (* cD |- cPhi     and     cD0, cD |- ms : cD ? *)

	 begin match candidates' with
	   | [] -> (dprint (fun () -> "[OPEN CONTEXT GOAL] " ^ P.dctxToString cD_cg cPhi_r) ;
		    dprint (fun () -> "[OPEN COVERAGE GOAL] " ^
			    P.patternToString cD_cg (gctxToCompgctx cG') pat'  );
	            open_cov_goals := (cD_cg, cG', pat')::!open_cov_goals ;
		    refine_pattern cgs cov_problem )
	   | _  ->
	      (dprint (fun () -> "  There are " ^ string_of_int (List.length candidates') ^
			 " refined candidates for " ^ P.patternToString cD (gctxToCompgctx cG) patt ^ "\n");
	       dprint (fun () -> candidatesToString (cD_cg, cG', candidates', pat')) ;
	       (cD_cg, cG', candidates', pat') :: refine_pattern cgs cov_problem)
	 end

let rec check_empty_pattern k candidates = match candidates with
  | [] -> []
  | Cand (cD_p, cG_p, ml, sl) :: cands ->
      let sl' = List.filter (fun (Split (CovGoal (_cPsi, tR, _sA) , patt)) ->
			       match patt with
				 | EmptyPatt (_cPhi, _sB) ->
				     (match tR with
					|LF.Root (_, LF.MVar (LF.Offset k', _ ), LF.Nil ) -> not (k = k' )
					| _ -> true)

				 | EmptyParamPatt (_cPhi, _sB) ->
				     (match tR with
					|LF.Root (_, LF.PVar (k', _ ), LF.Nil ) -> not (k = k' )
					| _ -> true)

				 | _ -> true )
	sl in
	Cand (cD_p, cG_p, ml, sl') :: check_empty_pattern k cands


(* ************************************************************************************* *)

(* TODO: Cleanup *)
(*  addToMCtx cD' (cD_tail, ms) = cD0, ms0

if cD' |- ms : cD
then  cD',{cD_tail}   |- ms0 : cD, cD_tail
      and ms0 is ms extended with the identity for declarations in cD_tail
*)

let rec addToMCtx cD (cD_tail, ms) = match cD_tail with
  | [] -> (cD , ms)
  | LF.Decl (u, LF.ClTyp (LF.MTyp tA, cPsi), dep) :: cD_tail ->
      let mdec = LF.Decl(u, LF.ClTyp (LF.MTyp (Whnf.cnormTyp (tA, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
        addToMCtx (LF.Dec (cD, mdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.Decl (u,  LF.ClTyp (LF.PTyp tA, cPsi), dep) :: cD_tail ->
      let pdec = LF.Decl(u,  LF.ClTyp (LF.PTyp (Whnf.cnormTyp (tA, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
        addToMCtx (LF.Dec (cD, pdec)) (cD_tail, Whnf.mvar_dot1 ms)
  | LF.Decl (u,  LF.ClTyp (LF.STyp (cl, cPhi), cPsi), dep) :: cD_tail ->
      let sdec = LF.Decl(u,  LF.ClTyp (LF.STyp (cl, Whnf.cnormDCtx (cPhi, ms)), Whnf.cnormDCtx (cPsi, ms)), dep) in
        addToMCtx (LF.Dec (cD, sdec)) (cD_tail, Whnf.mvar_dot1 ms)
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
	let mdec = LF.Decl (x, LF.ClTyp (LF.MTyp (LF.TClo(tP,ssi)), cPsi'), LF.Maybe) in
	let mv   = LF.Root(Syntax.Loc.ghost, LF.MVar(LF.Offset 1, Whnf.cnormSub  (ss', LF.MShift 1)), LF.Nil) in
	  (LF.Dec (cD'', mdec) , LF.Dot(LF.Obj mv, Whnf.cnormSub (s', LF.MShift 1)))

  (* genCtx elems = ctx_goal_list

     for each ctx_goal in ctx_goal_list .
        ctx_goal = (cD_i, cPsi_i, ms_i)  s.t.
        cO ; cD_i |- ms_i   : cD
        cO ; cD_i |- cPsi_i : ctx
  *)
  let rec genCtx  (LF.Dec (_cD', LF.Decl _ ) as cD) cpsi elems  = begin match elems with
    | [] -> [(cD, LF.Null, LF.MShift 0)]
    | LF.SchElem (decls, trec) :: elems ->
	let cPsi_list = genCtx cD cpsi elems in
	let d = Context.length decls in
	let (cD0, s)   = decTomdec cD cpsi (d-1, decls) in
	let _ = dprint (fun () -> "[genCtx] s = " ^ P.subToString cD0 cpsi s) in
	let cpsi' = LF.CtxVar (LF.CtxOffset (d+1)) in
         (* cD0 = cD, decls *)
	let tA = match trec with LF.SigmaLast(_, tA) -> LF.TClo (tA, s) | _ -> LF.TClo(LF.Sigma trec, s) in
	let _ = dprint (fun () -> "[genCtx] tA = " ^ P.typToString cD0 cpsi' (tA, S.LF.id)) in
	  (* cD0 ; cpsi |- tA : type *)
	(* let ms = gen_mid cD0 cD in *)
	let ms = LF.MShift ((Context.length cD0) - (Context.length cD)) in
        (* cD0 |- ms : cD
              cD' |- cPsi' ctx *)
	let cPsi'      = LF.DDec (cpsi', LF.TypDecl (new_bvar_name "x" , tA)) in

	let _ = dprint (fun () -> "[genCtx] cPsi' = " ^  P.dctxToString cD0 cPsi' ^ "\n") in
	let _ = dprint (fun () -> "         ms = " ^ P.msubToString cD0 ms ^ "\n") in
	let _ = dprint (fun () -> "         cD0 = " ^ P.mctxToString cD0 ^ "\n") in
	let _ = dprint (fun () -> "         cD = " ^ P.mctxToString cD ^ "\n") in
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
let genCtxGoals cD (LF.Decl(x, LF.CTyp (Some schema_cid), dep)) =
  let LF.Schema elems = Store.Cid.Schema.get_schema schema_cid in
  let cD'  = LF.Dec(cD, LF.Decl(x, LF.CTyp (Some schema_cid), dep)) in
    genCtx cD' (LF.CtxVar (LF.CtxOffset 1)) elems

let genContextGoals cD ctx_schema =
  let cgs = genCtxGoals cD ctx_schema in
    List.map (fun (cD, cPsi, ms) -> (cD, CovCtx cPsi, ms)) cgs

(* Find mvar to split on *)
let genSVCovGoals (cD, (cPsi, LF.STyp (r0, cPhi))) (* cov_problem *) = 
  begin match cPhi with 
    | LF.Null -> [(cD, CovSub (cPsi, LF.EmptySub, LF.STyp(r0, cPhi)),  LF.MShift 0)]
    | LF.CtxVar _ -> []  (* Split on the context variable first *)
    | LF.DDec (cPhi', decl) -> 
	let LF.TypDecl (x, tA) = decl in 
	let s      = LF.SVar(2, 0, Substitution.LF.id) in
	let mT     = LF.ClTyp(LF.STyp (r0, cPhi'), cPsi) in 
	let cD'    = LF.Dec(cD, LF.Decl(Id.mk_name(Whnf.newMTypName mT), mT, LF.No)) in
	  (* if ren = renaming, generate parameter variable *)
	let tM     = LF.Root(Syntax.Loc.ghost, LF.MVar(LF.Offset 1 , Substitution.LF.id), LF.Nil) in
	let tA0    = Whnf.cnormTyp (tA, LF.MShift 1) in  
	let cPhi0  = Whnf.cnormDCtx (cPhi', LF.MShift 1) in 
	let mT'    = LF.ClTyp(LF.MTyp tA0, cPhi0) in 
	let cD''   = LF.Dec(cD', LF.Decl(Id.mk_name(Whnf.newMTypName mT'),mT', LF.No)) in
	let cPsi'  = Whnf.cnormDCtx (cPsi, LF.MShift 2) in 
	let cPhi'' = Whnf.cnormDCtx (cPhi, LF.MShift 2) in
	  [(cD'', CovSub (cPsi', LF.Dot(LF.Obj tM, s), LF.STyp (r0, cPhi'')), LF.MShift 2)]
  end



let genCGoals (cD':LF.mctx) mdec = match mdec with
  | LF.Decl (_u, LF.ClTyp (LF.MTyp tA, cPsi), _) ->
      let _ = dprint (fun () -> "[SPLIT] CovGoal : " ^ P.dctxToString cD' cPsi ^ " . " ^
			P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in
      let dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
	(genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) , dep0)
  | LF.Decl (_u,  LF.ClTyp (LF.PTyp tA, cPsi), _) ->
      begin match cPsi with 
	| LF.CtxVar _ -> ([], Atomic)
         (* In the interactive mode, prevent splitting on parameter variables 
            whose type is simply a context variable and ask the user to split on
	    the context first; should maybe raise error. *)
	| _ -> 
	    let _ = dprint (fun () -> "[SPLIT] CovGoal (PVAR): " ^ P.dctxToString cD' cPsi ^ " . " ^
       			      P.typToString cD' cPsi (tA, S.LF.id) ^ "\n")  in
	    let dep0 = match tA with LF.Atom (_, _ , LF.Nil) -> Atomic | _ -> Dependent in
	      (* bp : This may potentially even loop! ;
       		 but this could initiate a potential split of PV including splitting the context
       		 g |- #A  should result in  g',x|- x   g',x|- #q
		 in this implementation, we assume that the context split has been done separetely,
       		 and hence we would only loop if we were to split #p (and initiate another context split)
              *)
       	      (genBCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)), dep0)
      end


  | LF.Decl (_u, LF.ClTyp (sTyp, cPsi), _ ) ->
      begin match cPsi with 
	| LF.CtxVar _ -> ([], Atomic)
      (* In the interactive mode, prevent splitting on substitution variables 
	 should be postponed until the domain, cPsi, has been refined and is 
	 either . (empty) or cPsi', _  
	 if cPsi is simply a context variable and ask the user to split on
	    the context first; should maybe raise Split error. *)
	| _ -> (genSVCovGoals (cD', (cPsi, sTyp)), Atomic)
      end


let rec best_ctx_cand (cD, cv_list) k cD_tail = match (cv_list, cD)  with
  | [], _  -> NoCandidate
  | [LF.CtxOffset j] , LF.Dec (cD', cd) ->
      if j = k then
	let ctx_goals = genCtxGoals cD' cd in
	let ctx_goals' = List.map (fun (cD', cPhi, ms) ->
				     (* cD' |- ms : cD *)
				     let ms' = LF.MDot (LF.CObj (cPhi),  ms) in
				     let k = List.length cD_tail in
				     let _ = dprint (fun () -> "[ctx_goal] cD' = " ^ P.mctxToString cD') in
				     let _ = dprint (fun () -> "[ctx_goal] ms' = " ^ P.msubToString cD' ms) in
				     let (cD'', ms0) = addToMCtx cD' (cD_tail, ms') in
				       (* cD', cD_tail |- ms0 : cD, cD_tail *)
				     let _ = dprint (fun () -> "[ctx_goal] " ^
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
				       let k = List.length cD_tail in
				       match cg with 
					 | CovGoal (cPsi', tR, sA') -> 
					     let _ = dprint (fun () -> "[Generated CovGoal]" ^ covGoalToString cD' cg) in
					     let ms' = LF.MDot (LF.ClObj ( Context.dctxToHat cPsi' , LF.MObj tR),  ms) in
					     let (cD'', ms0) = addToMCtx cD' (cD_tail, ms') in
					     let cg' = CovGoal (Whnf.cnormDCtx (cPsi', LF.MShift k) ,
								Whnf.cnorm (tR, LF.MShift k) ,
								(Whnf.cnormTyp (Whnf.normTyp sA' , LF.MShift k), S.LF.id)) in
					       TermCandidate (cD'' , cg',  ms0 )
					 | CovSub (cPhi,  s, sT) -> 
					     let ms' = LF.MDot (LF.ClObj (Context.dctxToHat cPhi, LF.SObj s), ms) in 
					     let (cD'', ms0) = addToMCtx cD' (cD_tail, ms') in
					     let cg' = CovSub (Whnf.cnormDCtx (cPhi, LF.MShift k),
							       Whnf.cnormSub (s, LF.MShift k), 
							       Whnf.cnormClTyp (sT, LF.MShift k)
							       ) in 
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


(* Implement function which generates coverage goals for general computation-level types *)
(* genPattSpine cD (tau_v, t) = (cD0, cG0, pS, ttau)

   if cD |- [t] tau_v

   then

      cD0 ; cG0 |- pS : [t]tau_v > ttau

*)
let rec genPattSpine (tau_v, t) = match (tau_v,t) with
  | (Comp.TypBool, t) ->
      ([], Comp.PatNil, (tau_v,t))

  | (Comp.TypArr (tau1, tau2) , t) ->
      let pv1 = new_patvar_name () in
      let pat1 = Comp.PatFVar (Syntax.Loc.ghost, pv1) in
      let (cG, pS, ttau) = genPattSpine (tau2,t) in
	((pv1, Whnf.cnormCTyp (tau1,t),false)::cG ,
	 Comp.PatApp (Syntax.Loc.ghost, pat1, pS), ttau)
  | (Comp.TypPiBox ((LF.Decl(x, LF.CTyp sW, _)), tau), t) ->
      let cPsi' = LF.CtxVar (LF.CInst ((x, ref None, LF.Empty, LF.CTyp sW, ref [], LF.Maybe), Whnf.m_id)) in
      let pat1 = Comp.PatMetaObj (Syntax.Loc.ghost,
				  (Syntax.Loc.ghost, LF.CObj cPsi')) in
      let (cG, pS, ttau0) = genPattSpine (tau, LF.MDot (LF.CObj(cPsi'), t)) in
	(cG, Comp.PatApp (Syntax.Loc.ghost, pat1, pS), ttau0)

  | (Comp.TypPiBox ((LF.Decl (u, LF.ClTyp (LF.MTyp tP,  cPsi), _)), tau), t) ->
      let tP' = Whnf.cnormTyp (tP, t) in
      let cPsi' = Whnf.cnormDCtx (cPsi,t) in
      let tR    = etaExpandMVstr LF.Empty cPsi' (tP', S.LF.id) in
      let pat1 = Comp.PatMetaObj (Syntax.Loc.ghost,
				  (Syntax.Loc.ghost, LF.ClObj(Context.dctxToHat cPsi', LF.MObj tR))) in
      let (cG, pS, ttau0) = genPattSpine (tau, LF.MDot (LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR), t)) in
	(cG, Comp.PatApp (Syntax.Loc.ghost, pat1, pS), ttau0)

  | (Comp.TypBox _ , t ) ->
      ( [], Comp.PatNil, (tau_v, t))
  | _ -> ( [], Comp.PatNil, (tau_v, t))

let genPatt (cD_p,tau_v) (c, tau_c) =
  let (cG, pS, (tau,t)) = genPattSpine  (tau_c, Whnf.m_id) in
  let pat = Comp.PatConst (Syntax.Loc.ghost, c, pS) in
  let _ = dprint (fun () -> "\n[genPatt] " ^ P.patternToString LF.Empty (gctxToCompgctx cG) pat ^
		    " : " ^ P.compTypToString LF.Empty (Whnf.cnormCTyp (tau,t))) in
  let _ = dprint (fun () -> "          expected type: " ^ P.compTypToString cD_p tau_v ^"\n") in
  let ms    = Ctxsub.mctxToMSub cD_p in
    begin try
      U.unifyCompTyp LF.Empty (tau,t) (tau_v, ms); 
      let (cD', cG', pat', tau', ms') = Abstract.covpatt 
	                                (Whnf.cnormCtx (gctxToCompgctx cG, Whnf.m_id)) 
					(Whnf.cnormPattern (pat, Whnf.m_id))
					(Whnf.cnormCTyp (tau_v, ms)) (Whnf.cnormMSub ms) in
      let ccG' = compgctxTogctx cG' in
	(dprint (fun () -> "[genPatt] - Return Coverage Pattern");
	Some (cD', CovPatt (ccG', pat', (tau', Whnf.m_id)), ms'))
    with U.Failure _ -> (* expected type and generated type for spine do not
			 unify; therefore c pS is not inhabit tau_v *)                       
                       None
      | Abstract.Error (_, Abstract.LeftoverConstraints) as e ->
	(print_string ("WARNING: Generation of pattern encountered left-over constraints in higher-order unification\n");
	 raise e)
    end

let rec genAllPatt ((cD_v, tau_v): LF.mctx * Comp.typ) ctau_list = match ctau_list with
  | [] -> []
  | (c,tau_c) :: ctau_list ->
      match genPatt (cD_v,tau_v) (c,tau_c) with
	| Some (cD,cg,ms) ->
	    let pat_list = genAllPatt (cD_v, tau_v) ctau_list
	    in (cD, cg, ms) :: pat_list
	| None -> genAllPatt (cD_v, tau_v) ctau_list

let genPatCGoals (cD:LF.mctx) (cG1:gctx) tau (cG2:gctx) = match tau with
  | Comp.TypBool ->
      let cG' = cG1@cG2 in
      let loc = Syntax.Loc.ghost in
      let cg_true = CovPatt (cG', Comp.PatTrue loc, (tau, Whnf.m_id)) in
      let cg_false = CovPatt (cG', Comp.PatFalse loc, (tau, Whnf.m_id)) in
	(cD, cg_true, Whnf.m_id) ::(cD, cg_false, Whnf.m_id) ::[]
  | Comp.TypCross (tau1, tau2) ->
      let pv1 = new_patvar_name () in
      let pv2 = new_patvar_name () in
      let cG1' = (pv1, tau1,false) :: (pv2,tau2,false):: cG1 in
      let cG' = cG1'@cG2 in
      let loc_ghost = Syntax.Loc.ghost in
      let pat = Comp.PatPair (loc_ghost,  Comp.PatFVar (loc_ghost, pv1), Comp.PatFVar (loc_ghost, pv2))  in
      let cg = CovPatt (cG', pat, (tau, Whnf.m_id)) in
	[ (cD, cg, Whnf.m_id) ]
  | Comp.TypBox (loc, (LF.ClTyp (LF.MTyp tA, cPsi) as mT)) ->
      let name = Id.mk_name (Whnf.newMTypName mT) in
      let (cgoals, _ ) = genCGoals cD (LF.Decl(name, LF.ClTyp (LF.MTyp tA, cPsi), LF.Maybe)) in

	List.map (fun (cD', cg, ms) ->
		    let CovGoal (cPsi', tR, sA') = cg in
		    let _ = dprint (fun () -> "[genPatCGoals] " ^
				      P.mctxToString cD' ^ " \n |- " ^
				      P.msubToString cD' ms ^ " \n : " ^
				      P.mctxToString cD) in
		    let ghost_loc = Syntax.Loc.ghost in
		    let pat_r = Comp.PatMetaObj (ghost_loc , (ghost_loc, LF.ClObj(Context.dctxToHat cPsi', LF.MObj tR))) in
	            let tau_r = (Comp.TypBox (loc, LF.ClTyp (LF.MTyp (LF.TClo sA'), cPsi')), Whnf.m_id) in
		    let cG' = cnormCtx (cG1, ms)@cnormCtx(cG2,ms) in
		    let _ = dprint (fun () -> "[genPatCGoals] " ^
				      "old cG = " ^ P.gctxToString cD (gctxToCompgctx (cG1@cG2))) in
		    let _ = dprint (fun () -> "[genPatCGoals] " ^
				      "new cG' = " ^ P.gctxToString cD' (gctxToCompgctx cG')) in
		      (cD', CovPatt (cG', pat_r, tau_r), ms)
		 )

	cgoals


  | Comp.TypBase (_, c, mS) ->
      let _ = dprint (fun () -> "\n[genPatCGoals] for " ^ P.compTypToString cD tau  ^ "\n") in
      let constructors = !((Store.Cid.CompTyp.get c).Store.Cid.CompTyp.constructors) in
      let _ = if constructors = [] then dprint (fun () -> "[genPatCGoals] No Constructors defined for " ^ P.compTypToString cD tau) else () in
      let constructors = List.rev constructors in
      let ctau_list   = List.map (function c ->
				    let tau_c = (Store.Cid.CompConst.get  c).Store.Cid.CompConst.typ in
	                              dprint (fun () -> R.render_cid_comp_const c ^ " : " ^
						P.compTypToString LF.Empty tau_c);
      	                              (c, tau_c)
						)
                                constructors
      in
      let r = 
	List.map (fun (cD, cg, ms) ->
		    let CovPatt (cG0, pat, ttau) = cg in
		    let cG0' = cnormCtx (cG1, ms)@cG0@ cnormCtx(cG2, ms) in
		      (cD, CovPatt (cG0', pat, ttau), ms))
	  (genAllPatt (cD,tau) ctau_list) in 
      let _ = dprint (fun () -> "\n[genPatCGoals] Generated " ^ string_of_int (List.length r) ^ " case(s) for " ^ P.compTypToString cD tau  ^ "\n") in
      let _ = dprint (fun () -> covGoalsToString r) in 
	r
  | _ -> []

(* best_candidate cO cD = cov_goals

   cov_goals is a list of coverage goals   CovGoal (cOD', cg, ms)

   where

   cg = CovGoal (cPsi, tR, sA) and   cOD' |- ms : cO;cD

*)

let rec mvInSplitCand cD vlist candidates = match candidates with
  | [] -> vlist
  | Cand(_, _, _ , sl) :: cands ->
      mvInSplitCand cD (mvInSplit cD vlist sl) cands

and mvInSplit cD vlist slist = match slist with
  | [] -> vlist
  | Split (CovGoal (_, LF.Root (_ , LF.MVar (u, _ ) , _ ), _ ), _ ) :: sl ->
      let (pvlist, cvlist , mvlist) = vlist in
      if List.mem u mvlist then
	mvInSplit cD vlist sl
      else mvInSplit cD (pvlist, cvlist, (u::mvlist)) sl

  | Split (CovGoal (_, LF.Root (_ , LF.PVar (k, _ ) , _ ), _ ), _ ) :: sl ->
      let (pvlist, cvlist , mvlist) = vlist in
      if List.mem (LF.Offset k) mvlist then
	mvInSplit cD vlist sl
      else
	(* we only split on a parameter variable, if its context is
           a proper context and not just a context variable *)
	(match Whnf.mctxPDec cD k with
	   | (_, _tA, LF.CtxVar _ ) -> 	mvInSplit cD (pvlist, cvlist, mvlist) sl
	   | _ -> 	mvInSplit cD (pvlist, cvlist, (LF.Offset k)::mvlist) sl)

  | Split (CovGoal (_, LF.Root (_ , LF.Proj (_ , _ ), _tS), _tA), _patt) :: sl ->
      mvInSplit cD vlist sl

  | Split (CovSub ( _ , LF.SVar (u, _ , _ ), _ ), _patt) :: sl -> 
      let (pvlist, cvlist , mvlist) = vlist in
      if List.mem (LF.Offset u) mvlist then
	mvInSplit cD vlist sl
      else mvInSplit cD (pvlist, cvlist, (LF.Offset u::mvlist)) sl

  | Split (_cg, _patt) :: sl ->
   (dprint (fun () -> "SPLIT CAND (other - an equation which was not solvable earlier due to constraints (for example pruning of a bound meta-variable is not possible) :\n");
    mvInSplit cD vlist sl)
(*      (dprint (fun () -> "SPLIT CAND (other - an equation which was not solvable earlier due to global constraints) :\n       " ^ covGoalToString cD cg ^ " == " ^
		 pattToString cD patt );
      raise (Error (Syntax.Loc.ghost, NothingToRefine)))
*)
  | SplitCtx (LF.CtxVar psi, cPhi) :: sl ->
      let (pvlist, cvlist , mvlist) = vlist in
(*	mvInSplit cD (psi::cvlist, mvlist) sl  *)
	if List.mem psi cvlist then
	mvInSplit cD (pvlist, cvlist, mvlist) sl
      else mvInSplit cD (pvlist, psi::cvlist, mvlist) sl

  | SplitPat ((Comp.PatFVar (_, x) , ttau) , (patt_p, ttau_p)) :: sl ->
      let (pvlist, cvlist , mvlist) = vlist in
	if List.mem x pvlist then
	  mvInSplit cD vlist sl
	else mvInSplit cD (x :: pvlist, cvlist, mvlist) sl

let best_split_candidate cD candidates =
  (* assume candidates are non-empty *)
  let (_pvsplit_list, cvsplit_list, mvsplit_list)  = mvInSplitCand cD ([], [], []) candidates in
   (* _pvsplit_list desribes the pattern variables one can split on,
      but we always split on pattern variables before calling best_split_candidate *)
  let mv_list_sorted = List.sort (fun (LF.Offset k) -> fun (LF.Offset k') ->
				    if k' < k then 1 else (if k' = k then 0 else -1))
                                 mvsplit_list in
  let cv_list_sorted = List.sort (fun (LF.CtxOffset k) -> fun (LF.CtxOffset k') ->
				    if k' < k then 1 else (if k' = k then 0 else -1))
                                 cvsplit_list in

(*  let _ = dprint (fun () -> "SHOW SPLIT CANIDATE LIST " ^ mvlistToString mv_list_sorted ) in *)
   if cv_list_sorted = [] then
     best_cand (cD, mv_list_sorted) 1 []
   else
     (dprint (fun () -> "Context Split possible\n") ;
      best_ctx_cand (cD, cv_list_sorted) 1 [])


(* ************************************************************************************* *)
(* refine_mv (cD, cG, candidates, patt) =

   if   cD ; cG |- patt
        and candidates = [(cD_p, cG_p, mE, sE), ... ]
        cG = Empty
   then
        refine the best candidate from cD using
        cD1 |- ms1 : cD, .... cDk |- msk : cD
        and generate k new coverage problems

*)
let refine_mv ( (cD, cG, candidates, patt) as cov_problem )  =
  begin match cD with
    | LF.Empty  ->
	((* print_string (candidatesToString cov_problem ) ; *)
	 open_cov_goals := (cD, cG, patt)::!open_cov_goals ;
	 raise (Error (Syntax.Loc.ghost, NothingToRefine))
	 (* [] *))
	(* raise (Error "Nothing to refine"))*)
    | _  ->
	let cov_goals' = best_split_candidate cD candidates in
	(* let _ = dprint (fun () -> "[Original candidates] \n" ^ candidatesToString cov_problem ) in *)
	  begin match (cov_goals', candidates ) with
	    | (SomeCtxCands ctx_goals, [] )  ->  []
	    | (SomeCtxCands ctx_goals,  _ )  ->
		(* bp : TODO refine_ctx_covproblem ctx_goals cov_problem *)
		(*	raise (Error "Context refinment not implemented yet") *)
		let _ = dprint (fun () -> "Some CtxCands ... ") in
              let cands = refine_pattern ctx_goals cov_problem in
              (dprint (fun () -> "[refine_pattern] done") ; cands)

	    | (SomeTermCands (_, []), [])  -> []
	    | (SomeTermCands (_, []), _ )  ->
		let _ = dprint (fun () -> "Check whether one of the candidates is empty ... ") in
		[(cD, [], check_empty_pattern 1 candidates, patt)]
	    | (SomeTermCands (_, cgoals), _ )  ->
		let _ = dprint (fun () ->
				  let cgs = List.map (fun (TermCandidate cg) -> cg) cgoals in
				    "#################################\n##### [Generated coverage goals] \n" ^
				      covGoalsToString cgs ) in
		let _ = dprint (fun () -> "for pattern " ^ P.patternToString cD (gctxToCompgctx cG) patt) in
		  refine_pattern cgoals cov_problem
(*		let Comp.PatMetaObj (_, mO) = patt in
		let (cPhi, tM) = match mO with
		  | Comp.MetaObjAnn (_, cPhi, tM) -> (cPhi, tM)
		  | Comp.MetaObj (loc, phat, tM) -> (Context.hatToDCtx phat, tM)
		in

		let lf_covproblem = (cD, cG, candidates, (cPhi, tM)) in
  		  refine_lf_covproblem cgoals lf_covproblem	*)
	    | (NoCandidate,   [] ) -> []
	    | (NoCandidate, _    ) -> (open_cov_goals := (cD, cG, patt) :: !open_cov_goals;[])
(*		let _ = dprint (fun () -> "No Candidates found: Remaining Candidates : \n" ^
				  candidatesToString (cD, candidates, (cPhi, tM) )) in
		raise (Error (Syntax.Loc.ghost, NoCoverageGoalsGenerated)) *)
	  end
  end

let rec subst_pattern (pat_r, pv) pattern = match pattern with
  | Comp.PatFVar (loc, y) ->
      if y = pv then pat_r else pattern
  | Comp.PatPair (loc, pat1, pat2) ->
      let pat1' = subst_pattern (pat_r, pv) pat1 in
      let pat2' = subst_pattern (pat_r, pv) pat2 in
	Comp.PatPair (loc, pat1', pat2')
  | Comp.PatAnn (loc, pat, tau) ->
      let pat' = subst_pattern (pat_r, pv) pat in
	Comp.PatAnn (loc, pat', tau)
  | Comp.PatConst (loc, c, pS) ->
      let pS' = subst_pattern_spine (pat_r, pv) pS in
	Comp.PatConst (loc, c, pS')
  | _ -> pattern

and subst_pattern_spine (pat_r, pv) pS = match pS with
  | Comp.PatNil -> Comp.PatNil
  | Comp.PatApp (loc, pat, pS) ->
      let pat' = subst_pattern (pat_r, pv) pat in
      let pS' = subst_pattern_spine (pat_r, pv) pS in
	Comp.PatApp (loc, pat', pS')

let rec subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml)  sl = match sl with
  | [] -> (ml, sl)
  | (SplitPat ((Comp.PatFVar (_, x), ttau), (patt_p, ttau_p)) as seqn) :: sl ->
      let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml)  sl in
	if x = pv then
	  (dprint (fun () -> "[subst_spliteqn] cD = " ^ P.mctxToString cD);
	    dprint (fun () -> "[subst_spliteqn] pat_r = " ^ 
		     P.patternToString cD (gctxToCompgctx cG) pat_r );
	   dprint (fun () -> "                 ttau = " ^ 
		     P.compTypToString cD   (Whnf.cnormCTyp ttau) ^ "!!!!!!\n");

	   dprint (fun () -> "[subst_spliteqn] cD_p = " ^ P.mctxToString cD_p);
	   dprint (fun () -> "[subst_spliteqn] pat_p = " ^ P.patternToString cD_p cG_p patt_p );
	   dprint (fun () -> "                 ttau_p = " ^  P.compTypToString cD_p   (Whnf.cnormCTyp ttau_p) ^ "!!!!!!\n");
	   dprint (fun () -> "[subst_spliteqn] ml' = " ^ eqnsToString cD cD_p   ml' ^ "\n");
	   match_pattern (cD, cG) (cD_p, cG_p) (pat_r, ttau) (patt_p, ttau_p) ml' sl')
	else
	  let ml', sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml)  sl in
	    (ml', seqn :: sl')
  | seqn :: sl ->
      let ml' , sl' = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml)  sl in
	(ml', seqn :: sl')

let rec subst_candidates (cD, cG) (pat_r, pv) candidates = match candidates with
  | [] -> []
  | Cand (cD_p, cG_p,ml, sl) :: cands ->
      let cands' = subst_candidates (cD, cG) (pat_r, pv) cands in
	begin try
	  let (ml', sl') = subst_spliteqn (cD, cG) (pat_r, pv) (cD_p, cG_p, ml) sl in
	    Cand (cD_p, cG_p,ml', sl') :: cands'
	with
	    Error (_, MatchError _) -> cands'
	end

let rec best_pv_cand' (cD, cG) pvlist (l, bestC) =
  match pvlist with
    | []  -> bestC
    | x :: pvlist ->
	let cov_goals' = genPatCGoals cD cG (lookup cG x) [] in
	let l' = List.length cov_goals' in
	  if l > l' then
	    best_pv_cand' (cD, cG) pvlist (l', (cov_goals' , x))
	  else
	     best_pv_cand' (cD, cG) pvlist (l, bestC)

let best_pv_cand (cD, cG) (x :: pvlist) =
  let cov_goals' = genPatCGoals cD cG (lookup cG x) [] in
  let _ = dprint (fun () -> "[genPatCGoals] for " ^ Id.render_name x ) in
  let _ = dprint (fun () -> covGoalsToString cov_goals') in
  let l = List.length cov_goals' in
    best_pv_cand' (cD, cG) pvlist (l, (cov_goals' , x))

(* find_splitCand sl  =  list of pattern variables which occur in a
   splitting equation on the left and hence are potential splitting candidates

*)

let rec pvInSplitCand sl pvlist  = match sl with
  | [] -> pvlist
  | Split (CovGoal _ , _ ) :: sl -> pvInSplitCand sl pvlist
  | Split (CovSub _ , _ ) :: sl -> pvInSplitCand sl pvlist
  | SplitCtx (_ , _ ) :: sl -> pvInSplitCand sl  pvlist
  | SplitPat ((Comp.PatFVar (_, x) , ttau) , (patt_p, ttau_p)) :: sl ->
      (dprint (fun () -> "[pvInSplitCand] Patttern variable " ^ Id.render_name x);
      if List.mem x pvlist then
	pvInSplitCand sl pvlist
      else pvInSplitCand sl (x::pvlist))

let rec pvInSplitCands candidates pvlist = match candidates with
  | [] -> pvlist
  | Cand(_, _, _ , sl) :: cands ->
      let pvlist' = pvInSplitCand sl pvlist in
	pvInSplitCands cands pvlist'

let rec refine_patt_cands ( (cD, cG, candidates, patt) as cov_problem ) (pvsplits, pv) = match pvsplits with
  | [] -> []
  | (cD', cg, ms) :: pvsplits ->
      let CovPatt (cG', pat_r , ttau) = cg in
      let _ = dprint (fun () -> "[refine_patt_cands] "
			^ "cD = " ^ P.mctxToString cD ^ "\n"
                        ^ "cG = " ^ P.gctxToString cD (gctxToCompgctx cG)
			^ "\nold pat = " ^
			P.patternToString cD (gctxToCompgctx cG) patt) in

      let _ = dprint (fun () -> "[refine_patt_cands] \n"
			^ "cD' = " ^ P.mctxToString cD'
			^ "\n cG' = " ^ P.gctxToString cD' (gctxToCompgctx cG')
                      ^ "\n[ms]pat = " ^
			P.patternToString cD' (gctxToCompgctx cG') (Whnf.cnormPattern (patt, ms))) in
      let patt' = subst_pattern (pat_r,pv) (Whnf.cnormPattern (patt, ms)) in
      let _ = dprint (fun () -> "[refine_patt_cands] new patt = " ^ P.patternToString cD' (gctxToCompgctx cG') patt') in
      let _ = dprint (fun () -> "ms = " ^ P.msubToString cD' ms  ^ "\n") in
      let candidates'  = refine_candidates (cD', cG', ms) (cD, cG, candidates) in
      let _ =  dprint (fun () -> "[refine_candidates] DONE : The remaining #refined candidates = " ^ string_of_int  (List.length candidates')) in
      let candidates'' = subst_candidates (cD', cG') (pat_r,pv) candidates' in
      let _ = dprint (fun () -> "[subst_candidates] DONE") in
      let r_cands      = refine_patt_cands cov_problem (pvsplits, pv) in
	(match candidates'' with
	   |  [] ->(open_cov_goals := (cD', cG', patt') :: !open_cov_goals;
		    r_cands)
	   | _ -> (cD', cG', candidates'', patt') :: r_cands
	)

let refine ( (cD, cG, candidates, patt) as cov_problem ) =
  begin match pvInSplitCands candidates [] with
    | [] ->
	(dprint (fun () -> "[refine] no pattern variables to refine - refine meta-variables");
         (* dprint (fun () ->  "[refine_mv] cov_problem : " ^ candidatesToString cov_problem ); *)
	refine_mv cov_problem  (* there are no pattern variables *))
    | pvlist ->  (* there are pattern variables to be split *)
	let _ = dprint (fun () -> "\n\n[refine] Pattern = " ^ P.patternToString cD (gctxToCompgctx cG) patt) in
	let _ = dprint (fun () -> "\n[refine] found " ^ string_of_int (List.length pvlist) ^ " candidates\n") in
	let (pv_splits, pv) = best_pv_cand (cD, cG) pvlist in
	let _ = dprint (fun () -> "\n[refine] Candidates generated " ^ string_of_int (List.length pv_splits) ^ " case(s) for \n" ^ 
			  candidatesToString cov_problem ^ "\n\n") in
	let r_cands =  refine_patt_cands cov_problem (pv_splits, pv) in
	let _ = dprint (fun () -> "\n[refine] refined cov_problem = " ) in
	let _ = List.map (fun (cD', cG', cands, patt) ->
			    (dprint (fun () -> "\n Pattern : " ^ P.patternToString cD' (gctxToCompgctx cG') patt);
			    dprint (fun () -> "\n Candidates : " ^
				      candidatesToString (cD', cG', cands, patt)
	                                  ^ "\n")))
	  r_cands
	in
	  r_cands
  end

let rec check_all f l = (match l with
(* iterate through l and collect all open coverage goals;
   f destructively updates open_cov_goals. *)
  | [] -> 
         (dprint (fun () ->  "*** [COVERAGE FAILURE] THERE ARE " ^ 
	       ("CASE(S) NOT COVERED :\n" ^ opengoalsToString (!open_cov_goals))
	       ^ "\n\n"))
  | h::t -> 
    ((f h) ; 
    check_all f t ))

(* At least one of the candidates in cand_list must be solvable,
   i.e. splitCand = []  and matchCand are solvable
*)


(* check_covproblem cov_problem = ()

   (cD, cG, candidates, cg) = cov_problem

   succeeds if there exists a candidate (Cand (cD_p, cG_p, matchCand, splitCand ))
   s.t. there are no splitCand and all matchCand can we solved using unification.

   otherwise

   will try to refine the given candidates and check coverage again.


   if there are candidates where there are no splitCandidate but matchCand
   cannot be solved, then add them to open_cov_goals, i.e. objects which are
   not covered.

*)
let rec check_covproblem cov_problem  =
  let ( cD , cG, candidates, cg) = cov_problem in
  (* existsCandidate candidates nCands open_cg
      Tries to see whether a given candidate is true, i.e.
      the pattern covers cg.

      If the pattern covers cg, coverage succeeds
      If the pattern does not cover cg, we add it to the open goals
      If the pattern does not YET cover cg, but it possibly can
      in the future, we extend nCands, the list of new candidates to consider.

  *)
  let rec existsCandidate candidates nCands open_cg =  match candidates with
    | [] ->
	let cov_prob' = (cD, cG, nCands, cg)  in
	let _         =  open_cov_goals := open_cg @ !open_cov_goals in
        let cp        = refine cov_prob' in
        (* Refine must make progress, i.e. cp =/= cov_problem,
           i.e. nCands must be different from the candidates of the original
           coverage problem *)
        (dprint (fun () -> "\nCheck Coverage (again) for " ^ covproblemsToString cp);
	  check_coverage cp)

    | ((Cand (cD_p, cG_p, matchCand, splitCand )) as c) :: cands ->
	(match splitCand with
	   |  [] ->
		let _ = dprint (fun () -> "\n\n #### [check_covproblem] CHECK WHETHER  " ^
                                  P.patternToString cD (gctxToCompgctx cG) cg ^" IS COVERED?\n") in
                let s_result = solve cD cD_p matchCand in
                   (match (s_result , U.unresolvedGlobalCnstrs ()) with
		   | (Solved, false) -> (* No new splitting candidates and all match
				  candidates are satisfied *)
			 dprint (fun () -> " \n #### [check_covproblem] COVERED " ^
				   P.patternToString cD (gctxToCompgctx cG) cg) ;
		       (* Coverage succeeds *)   ()

                   | (Solved, true) ->  (* No new splitting candidates, but leftover constraints *)
                                        (* Coverage Fails *)
		       let open_goal = (cD, cG, cg) in
		       existsCandidate cands nCands  (open_goal::open_cg)

		   | (PossSolvable cand, _ )  ->
                     (dprint (fun () -> "\n#### (A) NOT COVERED YET BUT THERE IS HOPE AND WE CAN SPLIT on ... ");
                      dprint (fun () -> "      " ^ candToString (cD, (gctxToCompgctx cG)) c);
		       (* Some equations in matchCand cannot be solved by hounif;
			  they will be resurrected as new splitting candidates *)
		       existsCandidate cands (cand :: nCands) open_cg)

		   | (NotSolvable, _ ) -> (* match candidates were not solvable;
                                             this candidate gives rise to coverage failure *)
                                          (* Coverage Fails *)
                     let _ = (dprint (fun () -> "\n**** (B) THE FOLLOWING CANDIDATE IS NOT COVERED ... " );
                              dprint (fun () -> "      " ^ candToString (cD, (gctxToCompgctx cG)) c)) in
		       let open_goal = (cD, cG, cg) in
	               (* open_cov_goals := ((cO, cD), cPhi,  tM)::!open_cov_goals ;  *)
		       existsCandidate cands nCands  (open_goal::open_cg)
		)
	   | _ ->  existsCandidate cands  (c :: nCands)  open_cg
	)
  in
    existsCandidate candidates [] [] 

and check_coverage (cov_problem_list : covproblems) =
  check_all (function  cov_prob -> check_covproblem cov_prob )   cov_problem_list


(* ****************************************************************************** *)

(* Flags *)
let enableCoverage = ref false  (* true iff coverage should be checked *)
let warningOnly    = ref false     (* true iff failed coverage should generate a warning *)
let no_covers = ref 0           (* number of times coverage checking has yielded a negative result *)

(* ****************************************************************************** *)
(* Printing for debugging *)


let trivially_empty_patt cD_p tau = 
  begin try 
    (match genPatCGoals cD_p [] tau [] with 
      | [] -> true
      | _ -> false)
  with _ -> false
  end 

let trivially_empty cov_problem =
  begin try
    begin match genCovGoals cov_problem with
      | [] -> true
      | _  -> false
    end
  with Abstract.Error _ -> (print_endline "Unable to prove remaining open coverage goals trivially empty due to higher-order constraints." ; false)
  end

let trivially_empty_param cov_problem =
  begin try
    begin match genPVar cov_problem with
      | [] -> true
      | _  -> false
    end
  with Abstract.Error _ -> (print_endline "Unable to prove remaining open coverage goals trivially empty due to higher-order constraints." ; false)
  end






let rec extract_patterns tau branch_patt = match branch_patt with
  | Comp.Branch (loc, cD, _cG, Comp.PatAnn (loc', pat, _), ms, _e) ->
      extract_patterns tau (Comp.Branch (loc, cD, _cG, pat, ms, _e))

  | Comp.EmptyBranch (loc, cD, Comp.PatEmpty (loc', cPsi), ms)  ->
      begin match tau with
        | Comp.TypBox (_, LF.ClTyp (LF.MTyp tA, cPhi)) -> (cD, EmptyPatt (cPsi, (Whnf.cnormTyp (tA, ms), S.LF.id)))
        | Comp.TypBox (_, LF.ClTyp (LF.PTyp tA, cPhi)) -> (cD, EmptyParamPatt (cPsi, (Whnf.cnormTyp (tA, ms), S.LF.id)))
	    (* Add EmptySubPatt *)
	| Comp.TypBase (_, c, mS) -> (cD, EmptyCompPatt (tau, ms))
      end

  | Comp.Branch (loc, cD, cG, pat, ms, _e) ->
      (cD, GenPatt (cG, pat, (tau, ms)))



let rec gen_candidates loc cD covGoal patList = match patList with
  | [] -> []
  | (cD_p, EmptyPatt (cPsi, sA) ) :: plist ->
      if trivially_empty (cD_p, cPsi, Whnf.normTyp sA) then
	gen_candidates loc cD covGoal plist
      else
	raise (Error (loc, NoCover
			(Printf.sprintf "\n##   Empty Pattern ##\n \n##   Case expression of type : \n##   %s\n##   is not empty.\n\n"
			   (P.typToString cD_p cPsi sA))))

  | (cD_p, EmptyParamPatt (cPsi, sA) ) :: plist ->
      if trivially_empty_param (cD_p, cPsi, Whnf.normTyp sA) then
	gen_candidates loc cD covGoal plist
      else
	raise (Error (loc, NoCover
			(Printf.sprintf "\n##   Empty Parameter Pattern ##\n \n##   Case expression of parameter type : \n##   %s\n##   is not empty.\n\n"
			   (P.typToString cD_p cPsi sA))))

  | (cD_p, EmptyCompPatt ttau) :: plist -> 
      let tau = Whnf.cnormCTyp ttau in 
      if trivially_empty_patt cD_p tau then 
	gen_candidates loc cD covGoal plist
      else 
	raise (Error (loc, NoCover
			(Printf.sprintf "\n##   Empty Pattern ##\n \n##   Case expression of type : \n##   %s\n##   is not empty.\n\n"
			   (P.compTypToString cD_p tau))))


  | (cD_p, GenPatt (cG_p, pat, ttau)) :: plist ->
      let CovPatt (cG', pat', ttau') = covGoal in
      let ml , sl = match_pattern (cD, cG') (cD_p, cG_p) (pat', ttau') (pat, ttau) [] [] in
	Cand (cD_p, cG_p, ml, sl) :: gen_candidates loc cD covGoal plist


(* initialize_coverage problem =

*)
let initialize_coverage problem projOpt = begin match problem.ctype with

  | Comp.TypBox(loc, LF.CTyp w) ->
      let cD'        = LF.Dec (problem.cD, LF.Decl(Id.mk_name (Whnf.newMTypName (LF.CTyp w)), LF.CTyp w, LF.Maybe)) in
      let cG'        = cnormCtx (problem.cG, LF.MShift 1) in
      let cPsi       = LF.CtxVar (LF.CtxOffset 1) in 
      (* let covGoal    = CovPatt(LF.Empty, Comp.PatMetaObj (loc,LF.CObj cPsi)) in  *)
      let loc'       = Syntax.Loc.ghost in
      let mC         = Comp.PatMetaObj(loc', (loc',LF.CObj cPsi)) in 
      let mT         = Comp.TypBox(loc, LF.CTyp w) in
      let covGoal    = CovPatt ([], mC, (mT, LF.MShift 0)) in
      let pat_list  = List.map (function b -> extract_patterns problem.ctype b) problem.branches in
      let cand_list =  gen_candidates problem.loc cD' covGoal pat_list in
	[ ( cD', cG', cand_list,  mC) ]

  | Comp.TypBox(loc, LF.ClTyp (LF.MTyp tA, cPsi)) ->
      let (s, (cPsi', tA')) = gen_str problem.cD cPsi tA in 
	(*  cPsi |- s  : cPsi' *)
      let mT         =  LF.ClTyp (LF.MTyp tA', cPsi') in
      let name       = Id.mk_name (Whnf.newMTypName mT) in
      let cD'        = LF.Dec (problem.cD, LF.Decl(name, mT, LF.Maybe)) in
      let cG'        = cnormCtx (problem.cG, LF.MShift 1) in
      let mv         = LF.MVar (LF.Offset 1, s) in
      let tM         = LF.Root (Syntax.Loc.ghost, mv, LF.Nil) in
      let cPsi       = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
      let tA         = Whnf.cnormTyp (tA, LF.MShift 1) in
      let loc'       = Syntax.Loc.ghost in
      let mC         = Comp.PatMetaObj(loc', (loc, LF.ClObj(Context.dctxToHat cPsi, LF.MObj tM))) in 
      let mT         = Comp.TypBox(loc, LF.ClTyp (LF.MTyp tA, cPsi)) in
      let covGoal    = CovPatt ([], mC, (mT, LF.MShift 0)) in
      (* let covGoal    = CovGoal (cPsi, tM, (tA, S.LF.id)) in *)
(*      let _          = print_string "\nGenerated Coverage goal: " in
      let _          = print_string (covGoalToString cD' covGoal) in
      let _          = print_string ("\n cD' = " ^ P.mctxToString cD' ^ "\n") in
      let _          = print_string "\n\n" in
*)
      let pat_list  = List.map (function b -> extract_patterns problem.ctype b) problem.branches in

      let cand_list =  gen_candidates problem.loc cD' covGoal pat_list in
      [ ( cD' , cG', cand_list , mC) ]

  | Comp.TypBox(loc, LF.ClTyp (LF.PTyp tA, cPsi)) ->
      let (s, (cPsi', tA')) = gen_str problem.cD cPsi tA in
      let mT         = LF.ClTyp (LF.PTyp tA', cPsi') in
      let cD'        = LF.Dec (problem.cD, LF.Decl(Id.mk_name (Whnf.newMTypName mT),  mT, LF.Maybe)) in
      let cG'        = cnormCtx (problem.cG, LF.MShift 1) in
      let mv         = match projOpt with None -> LF.PVar (1, s) | Some k -> LF.Proj(LF.PVar (1, s), k) in
      let tM         = LF.Root (Syntax.Loc.ghost, mv, LF.Nil) in
      let cPsi       = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
      let tA         = Whnf.cnormTyp (tA, LF.MShift 1) in
      let loc'       = Syntax.Loc.ghost in
      let mC         = Comp.PatMetaObj(loc', (loc', LF.ClObj (Context.dctxToHat cPsi, LF.MObj tM) )) in
      let mT         = Comp.TypBox(loc, LF.ClTyp (LF.PTyp tA, cPsi)) in
      let covGoal    = CovPatt ([], mC, (mT, LF.MShift 0)) in
      let pat_list   = List.map (function b -> extract_patterns problem.ctype b) problem.branches in
      let cand_list  =  gen_candidates problem.loc cD' covGoal pat_list in
      [ ( cD' , cG', cand_list , mC) ]

  | Comp.TypBox(loc, ((LF.ClTyp (LF.STyp (r, cPhi), cPsi)) as mT)) ->
      let cD'       = LF.Dec (problem.cD, LF.Decl(Id.mk_name (Whnf.newMTypName mT),  mT, LF.Maybe)) in
      let cG'       = cnormCtx (problem.cG, LF.MShift 1) in
      let s         = LF.SVar(1, 0, Substitution.LF.id) in
      let cPhi      = Whnf.cnormDCtx (cPhi, LF.MShift 1) in
      let cPsi      = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
      let loc'      = Syntax.Loc.ghost in
      let mC        = Comp.PatMetaObj(loc' , (loc', LF.ClObj (Context.dctxToHat cPhi, LF.SObj s) )) in
      let mT        = Comp.TypBox(loc, ((LF.ClTyp (LF.STyp (r, cPhi), cPsi)))) in
      let covGoal    = CovPatt ([], mC, (mT, LF.MShift 0)) in

      let pat_list  = List.map (function b -> extract_patterns problem.ctype b) problem.branches in

      let cand_list =  gen_candidates problem.loc cD' covGoal pat_list in

      [ ( cD' , cG', cand_list , mC) ]
	

 | tau ->  (* tau := Bool | Cross (tau1, tau2) | U *)
      let loc_ghost = Syntax.Loc.ghost in
      let pv = new_patvar_name () in
      let cG' = (pv, tau,false ) :: problem.cG in
      let pat = Comp.PatFVar (loc_ghost, pv) in
      let pat_list = List.map (function b -> extract_patterns problem.ctype b) problem.branches in
      let covGoal = CovPatt (cG', pat, (problem.ctype, Whnf.m_id)) in
      let cand_list = gen_candidates problem.loc problem.cD covGoal pat_list in
	[ (problem.cD, cG', cand_list, pat) ]

end

(* check_emptiness cD = bool
   if for all declarations X:U in cD such that
   splitting on X yields no candidates
*)

let rec check_emptiness cD = match cD with
  | LF.Empty -> false
  | LF.Dec(cD', (LF.Decl (_u, LF.ClTyp (LF.MTyp tA, cPsi), _) as cdecl) ) ->
      begin try
	(match genCovGoals (cD', cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> (dprint (fun () -> "[check_emptiness of cD] " ^ P.cdeclToString cD' cdecl ^ " is empty");  true)
	   | _  -> check_emptiness cD'
	)
      with Abstract.Error (_, msg) ->
	print_endline ("Unable to prove : " ^ P.typToString cD' cPsi (tA, S.LF.id) ^ " to be empty") ;
	print_endline "Try next meta-variable ...";
	check_emptiness cD'
      end
  | LF.Dec(cD', LF.Decl (_u,  LF.ClTyp (LF.PTyp LF.Sigma _ , _cPsi), _)) ->
      check_emptiness cD'
  | LF.Dec(cD', LF.Decl (_u,  LF.ClTyp (LF.PTyp tA, cPsi), _)) ->
      begin try
	(match genBCovGoals (cD' , cPsi, Whnf.normTyp (tA, S.LF.id)) with
	   | [] -> true
	   | _  -> check_emptiness cD'
	)
      with Abstract.Error (_, msg) ->
	print_string "Unable to prove given type is empty\n" ; check_emptiness cD'
      end

  | LF.Dec (cD', LF.Decl _ ) -> check_emptiness cD'


let rec check_empty_comp cD cG = match cG with
  | [] -> false
  | (_x, tau, _)::cG ->
      begin try
        let cov_goals' = genPatCGoals cD cG tau [] in
          match  cov_goals' with
            | [] -> true
            | _ -> check_empty_comp cD cG
      with _ -> check_empty_comp cD cG
      end

let rec revisit_opengoals ogoals = begin match ogoals with
  | [] -> ([], [])
  | ((cD, cG, _patt) as og) :: ogoals ->
      dprint (fun () -> "REVISIT OPEN GOAL: " ^ opengoalToString og);
      let _ = U.resetGlobalCnstrs () in
      if check_emptiness cD then
	let _ = dprint (fun () -> "cD = " ^ P.mctxToString cD ^ "\n contains an assumption of empty type.") in 
        let (oglist , trivial_list) = revisit_opengoals ogoals in
	  (oglist, og::trivial_list)
      else
        if check_empty_comp cD cG then
	let _ = dprint (fun () -> "cG = " ^ P.gctxToString cD (gctxToCompgctx cG) ^ "\n contains an assumption of empty type.") in 
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
	(dprint (fun () -> "\n ###### COVERS ####### \n ");
	 Success)
      else
	(* Check if the open coverage goals can be proven to be impossible *)
	Failure (Printf.sprintf "    %s\n\n"
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
              cD : LF.mctx ; cG ;
              branches ; ctype : tau }

  where   cD ; cPsi |- tA

  Succeeds, if there is at least one pattern which covers elements of type tau
  Fails, otherwise
*)
let covers problem projObj =
if !Total.enabled || !enableCoverage then
 (if trivial_coverage problem.cD problem.branches problem.ctype then
   ((* print_string "Trival Coverage\n"; *)
    Success)
  else
    (let _ = dprint (fun () -> "\n #################################\n ### BEGIN COVERAGE FOR TYPE tau = " ^
		       P.compTypToString problem.cD problem.ctype) in
     let _ = (Debug.pushIndentationLevel(); Debug.indent 2) in
     let _ = U.resetGlobalCnstrs () in
    (* *********************************************************************** *)
     let cov_problems : covproblems = initialize_coverage problem projObj in
    (* *********************************************************************** *)
       dprint (fun () -> "Coverage checking a case with "
		 ^ string_of_int (List.length problem.branches)
		 ^ " branch(es) at:\n"
		 ^ Syntax.Loc.to_string problem.loc);

       dprint (fun () -> "\n ### Initial coverage problem: " );
       dprint (fun () -> covproblemsToString cov_problems ) ;
    (* ********************************************************************** *)
       check_coverage cov_problems ;  
    (* ********************************************************************** *)
       dprint (fun () -> "*** !!! COVERAGE CHECKING COMPLETED – Check whether some open coverage goals are trivial. !!!*** ");
       dprint (fun () ->  "*** !!! " ^ 
	       ("REVISIT :\n" ^ opengoalsToString (!open_cov_goals))
	       ^ "\n\n");
       let o_cg         = !open_cov_goals in
       let (revisited_og, trivial_og) = revisit_opengoals o_cg in

	 (*        let r            = List.length  o_cg in
		   let r'           = List.length (revisited_og) in
		   if r  > r' then
	   ((* print_endline "\n(Some) coverage goals were trivially proven to be impossible.";
	    print_endline ("CASES TRIVIALLY COVERED in line " ^
			     Syntax.Loc.to_string  problem.loc
			   ^ " : " ^ string_of_int (List.length (trivial_og)));
	    print_string ("\nTRIVIAL OPEN GOALS:\n" ^  opengoalsToString trivial_og ^ "\n")*)
	   )
	 else () ;*)

    open_cov_goals :=  revisited_og ;
    check_coverage_success problem
  )
 )
else
  Success



let process problem projObj  =
  reset_cov_problem () ;
  match covers problem projObj with
  | Success -> reset_counter ()
  | Failure message ->
      (reset_counter () ;
      if !warningOnly then
        (print_string "WARNING: CASES DID NOT COVER\n";
        Error.addInformation ("WARNING: Cases didn't cover: " ^ message))
      else
        raise (Error (problem.loc, NoCover message)))



let problems = ref ([] : problem list)
(*
let clear () =
  problems := []

let stage problem =
  problems := problem::!problems
*)
let force f =
  (match !problems with [] -> []
     | _ ->   List.map (fun problem -> f (covers problem None)) (List.rev !problems))
