(* module Interactive *)

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp
module Cover = Coverage
module S = Substitution
open Syntax.Int.Comp

 let (dprint, _) = 
 Debug.makeFunctions (Debug.toFlags [29])


(*********************)
(* helper functions *)
(*********************)
let rec gctxToCompgctx cG = match cG with
  | [] -> LF.Empty
  | (x,tau) :: cG ->
      LF.Dec(gctxToCompgctx cG, Comp.CTypDecl (x, tau))

(* drop the first i element of cD *)
let rec dropIMCtx i cD = match (i, cD) with
| (1, LF.Dec (cD', _)) -> cD'
| (i, LF.Dec (cD', a)) ->
   let cD' = dropIMCtx (i-1) cD' in
   LF.Dec (cD', a)
| _ -> failwith "dropIMCtx removed more than the context could take"

(* insert mfront as the ith element of ms *)
let rec insertIMSub i mfront ms = match (i, ms) with
| (1, ms) -> LF.MDot (mfront, ms)
| (i, LF.MDot (mf, ms')) ->
   let ms' = insertIMSub (i-1) mfront ms' in
   LF.MDot(mf, ms')
| (i, LF.MShift k ) ->
    insertIMSub i mfront (LF.MDot (LF.MV(k+1), LF.MShift(k+1)))


let nameOfLFcTypDecl = (function
| LF.Decl(n, _, _) -> n
| LF.DeclOpt n -> n)

let cvarOfLFcTypDecl td =
 match td with
| LF.Decl(n, _, _) -> n
| LF.DeclOpt(n) -> n

let nameOfCompcTypDecl = function
  | CTypDecl (n, _) -> n
  | CTypDeclOpt n -> n

let rec dctxToHat cPsi = match cPsi with
| LF.Null -> (None, 0)
| LF.CtxVar cvar -> (Some cvar, 0)
| LF.DDec (cPsi', _) ->
   let (cV, i) = dctxToHat cPsi' in
   (cV, i+1)

let rec gctxToVars cG = match cG with
| LF.Dec (cG' , td) ->
    let vars' = gctxToVars cG' in
     Store.Var.extend vars' (Store.Var.mk_entry (nameOfCompcTypDecl td))
| LF.Empty  -> Store.Var.create ()

let rec mctxToCVars cD = match cD with
| LF.Dec (cD', td) ->
    let vars' = mctxToCVars cD' in
     Store.CVar.extend vars' (Store.CVar.mk_entry (cvarOfLFcTypDecl td))
| LF.Empty  -> Store.CVar.create ()

(*   and dctx =                                 (* LF Context                     *)
    | Null                                   (* Psi ::= .                      *)
    | CtxVar   of ctx_var                    | psi
    | DDec     of dctx * typ_decl            (* | Psi, x:A   or x:block ...    *)

let rec psiToM = function
| LF.Null -> failwith "IDK"
| LF.DDec(psi', LF.TypDecl(n, tA)) ->
| LF.DDec(psi', LF.TypDeclOpt(n)) ->
 *)
let printCtxGoal (cD,cPsi,mS) =
" ["^P.dctxToString cD cPsi^"]"

let printCovGoals cgs =
  let imp = !(Pretty.Control.printImplicit) in
  Pretty.Control.printImplicit := false;
  let strl = List.map (fun (cD,cg, _) ->  match cg with
  | Cover.CovGoal(cPsi, tR, sA) ->
      "["^P.dctxToString cD cPsi ^ " |- " ^
      P.normalToString cD cPsi (tR, S.LF.id)^ "]"
  | Cover.CovPatt (cG, patt, ttau) ->
      P.patternToString cD (gctxToCompgctx cG) patt
        ) cgs in
  Pretty.Control.printImplicit := imp;
  strl

let rec compgctxTogctx ccG = match ccG with
| LF.Empty -> []
| LF.Dec (ccG', Comp.CTypDecl (x,tau)) ->
    let cG' = compgctxTogctx ccG' in
    (x,tau)::cG'


let rec gctxToCompgctx cG = match cG with
  | [] -> LF.Empty
  | (x,tau) :: cG ->
      LF.Dec(gctxToCompgctx cG, Comp.CTypDecl (x, tau))

let locCount = ref 0

let locCount () =
  let e = !locCount in
  locCount := e + 1;
  e

let nextLoc loc =
            let (file_name,
                 start_line,
                 _start_bol,
                 start_off,
                 stop_line,
                 stop_bol,
                 stop_off,
                 _ghost) = Loc.to_tuple loc in
            Loc.of_tuple (file_name, start_line, min_int + locCount(), start_off, stop_line, stop_bol, stop_off, true)


(* loc -> (LF.mctx * cov_goal * LF.msub) list -> (Comp.typ x LF.msub) -> Comp.branch list *)
(*  branchCovGoals loc n cG0 tA cgs =
    cD', cD0 |- tA with |cD0| = n
    for all (cD_i , cg_i, ms_i)  in cg,
      cD_i |- ms_i : cD'
*)
let branchCovGoals loc i cG0 tau cgs =
  List.map (fun (cD, cg, ms) ->  match cg with
  | Cover.CovCtx cPsi ->
      let loc' = nextLoc loc in
      (* Printf.printf "CovGoal %s with msub =  %s and i = %s\n"  (P.dctxToString cD cPsi) (P.msubToString cD ms) (string_of_int i); *)
      Holes.collect(loc', cD, Whnf.cnormCtx(cG0, ms) , (tau, ms));
     let patt = PatMetaObj ( Loc.ghost, (Loc.ghost, LF.CObj cPsi)) in
       Comp.Branch(Loc.ghost, cD, LF.Empty, patt, ms,Comp.Hole (loc', (fun () -> Holes.getHoleNum loc')))
  | Cover.CovGoal(cPsi, tR, _tau' ) ->
      let loc' = nextLoc loc in
       (* Printf.printf "CovGoal: %s \n"  (P.msubToString cD ms); flush stderr; *)
     (* _tau'  = tau[ms] *)
      Holes.collect(loc', cD, Whnf.cnormCtx(cG0, ms) , (tau, ms));
     let patt = PatMetaObj ( Loc.ghost, (Loc.ghost, LF.ClObj(Context.dctxToHat cPsi, LF.MObj tR))) in
       Comp.Branch(Loc.ghost, cD, LF.Empty, patt, ms,Comp.Hole (loc', (fun () -> Holes.getHoleNum loc')))

  | Cover.CovPatt (cG, patt, (_tau',ms')) ->
      let loc' = nextLoc loc in
(*       Printf.printf "CovPat %s \n" (P.msubToString cD ms); *)
      Holes.collect(loc', cD, gctxToCompgctx cG,  (tau, ms));
      Comp.Branch(Loc.ghost, cD, gctxToCompgctx cG , patt, ms, Comp.Hole (loc', (fun () -> Holes.getHoleNum loc')))
        ) cgs

let matchFromPatterns l e bl =
   Comp.Case(l, Pragma.RegularCase, e, bl)


let genVarName tA = Store.Cid.Typ.gen_var_name tA


let rec mapHoleChk f = function
 | Hole (l, e) ->
     f l e
 | If (l, es,ec1,ec2) ->
     let es' = mapHoleSyn f es in
     let ec1' = mapHoleChk f ec1 in
     let ec2' = mapHoleChk f ec2 in
     If(l, es', ec1', ec2')
 | Syn (l, es) ->
     let es' = mapHoleSyn f es in
         Syn (l, es')
 | Rec (l, n, ec) ->
    let ec' =  mapHoleChk f ec in
    Rec (l, n, ec')
 | Fn (l, n, ec) ->
    let ec' =  mapHoleChk f ec in
    Fn(l, n, ec')
 | MLam (l, n, ec) ->
   let ec' =  mapHoleChk f ec in
   MLam (l, n, ec')
 | Let (t, es, (n, ec)) ->
     let es' =  mapHoleSyn f es in
     let ec' = mapHoleChk f ec  in
     Let(t, es', (n, ec'))
 | LetPair (t, es, (n1,n2, ec)) ->
     let es' =  mapHoleSyn f es in
     let ec' =   mapHoleChk f ec in
     LetPair(t,es', (n1,n2,ec'))
 | Pair (l,  ec1, ec2) ->
     let ec1' = mapHoleChk f ec1 in
     let ec2' = mapHoleChk f ec2 in
     Pair(l, ec1', ec2')
 | Case (l, s, es, bs) ->
     let es' = mapHoleSyn f es in
     let bs' = List.map (mapHoleBranch f) bs in
     Case(l,s,es', bs')
 |  e -> e
and mapHoleSyn f = function
  | Apply (l, es, ec) ->
      let es' = mapHoleSyn f es in
      let ec' = mapHoleChk f ec in
      Apply(l, es', ec')
  | MApp (l, es, c) ->
     let es' =  mapHoleSyn f es in
     MApp(l, es', c)
  | Ann (ec, tau) ->
      let ec' =  mapHoleChk f ec in
      Ann(ec', tau)
  | Equal (l, es1, es2) ->
      let es1' = mapHoleSyn f es1 in
      let es2' = mapHoleSyn f es2 in
      Equal(l, es1', es2')
  | PairVal(l, es1, es2) ->
      let es1' =  mapHoleSyn f es1 in
      let es2' = mapHoleSyn f es2 in
      PairVal(l, es1', es2')
  | e -> e
and mapHoleBranch f = function
  | Branch (l, cD, cG, p, mS, ec) ->
      let ec' =  mapHoleChk f ec  in
      Branch (l, cD, cG, p, mS, ec')
  | e -> e
(*   %% deprecated
| BranchSBox (l, cD1, cD2, cG, ec) ->
     let ec' =  mapHoleChk f ec in
     BranchSBox (l, cD1, cD2, cG, ec')
  | BranchBox (l, cD, (cPsi, NormalPattern( n, ec), ms, tA)) ->
     let ec' =  mapHoleChk f ec in
     BranchBox (l, cD, (cPsi, NormalPattern (n, ec'), ms, tA)) *)



(* replaces the ith hole (appearing in a function) with exp, overwriting the previous definition of the function *)
let replaceHole i exp =

(* test if Hole(l',f) is the ith hole, in which case
* detroy previous hole, commit staged holes and return the expression
* otherwise (not ith) returns back Hole(l',f)
* IMPORTANT: Check.comp.check that exp fits the holes beforehand *)
  let ithHoler l exp l' f =
    if (l = l') then
      (Holes.destroyHoles(l); Holes.commitHoles(); exp)
    else Synint.Comp.Hole(l',f) in

  let funOfHole i =
    let (loc, _cD, _cG, (_tau, _mS)) = Holes.getOneHole i in
    let entries = DynArray.to_list Store.Cid.Comp.entry_list in
    let opt =
      List.fold_left (fun found_opt entries' ->
        match found_opt with
        | None ->
          begin try
            Some(List.find (fun (_,loc') -> Holes.locWithin loc' loc) !entries')
          with _ -> None end
        | Some _ -> found_opt) None entries in
    match opt with
    | Some (cid_prog, loc') -> (Store.Cid.Comp.get cid_prog, loc')
    | _ -> failwith "Error in Interactive.funOfHole" in

  let (entry, loc) = funOfHole i in
  let Some lh = Holes.getHolePos i in
  (match entry.Store.Cid.Comp.prog with
  | Synint.Comp.RecValue (prog, ec, ms, env) ->
      let ec' = (mapHoleChk (ithHoler lh exp) ec) in
      let _l = Store.Cid.Comp.add loc
          (fun cid ->
            Store.Cid.Comp.mk_entry
	      entry.Store.Cid.Comp.name
	      entry.Store.Cid.Comp.typ
	      entry.Store.Cid.Comp.implicit_arguments
	      entry.Store.Cid.Comp.total
              (Synint.Comp.RecValue (cid, ec', ms, env))
              entry.Store.Cid.Comp.mut_rec) in
      P.ppr_sgn_decl (Synint.Sgn.Rec [(prog,entry.Store.Cid.Comp.typ ,ec')])
  | _ -> Holes.stashHoles (); failwith ("Error in replaceHole: "^(Id.string_of_name entry.Store.Cid.Comp.name)^" is not a function\n")  )





(*********************)
(* top level tactics *)
(*********************)




(* intro: int -> Comp.exp_chk option *)
let is_inferred = function
| LF.Decl(_, ctyp, dep) ->
    begin match dep with
      | LF.No -> false
      | LF.Maybe -> true
    end
| _ -> false

let  intro i =
  let used = ref false in
  let (loc, cDT, cGT, (tau, mS)) = Holes.getOneHole i in
  let rec crawl cD cG  = (function
 | Comp.TypArr (t1,t2) ->
     ( match t1 with
     | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA,psi)) ->
         used := true;
         let nam = Id.mk_name (Id.BVarName (genVarName tA)) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fn(l, nam, exp))
     | Comp.TypBox (l, LF.ClTyp (LF.PTyp tA,psi)) ->
         used := true;
         let nam = Id.mk_name (Id.PVarName (genVarName tA)) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fn(l, nam, exp))
     | _ ->
         used := true;
         let nam = Id.mk_name (Id.NoName) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fn(Loc.ghost, nam, exp))
           )
 | Comp.TypPiBox (tdec, t') when not (is_inferred tdec) ->
     used := true;
     let nam = nameOfLFcTypDecl tdec in
     let Some exp = crawl (LF.Dec (cD, tdec)) cG t' in
     Some (Comp.MLam (Loc.ghost, nam , exp))
 | t ->
     if !used then
       let loc' = nextLoc loc in
       Holes.collect(loc', cD, cG, (t, mS));
       Some (Comp.Hole  (loc', (fun () -> Holes.getHoleNum loc')))
     else None
         ) in
  crawl cDT cGT tau






(* search: Int.LF.typ -> string option *)

let search tA =
  let (tA', i) = Monitor.timer ("Constant Abstraction",
                                fun () -> Abstract.typ tA) in
  Logic.runLogicOn (Some (Id.mk_name (Id.SomeString "L"))) (tA', i) None (Some 1)



(* genCGoals cD' cd cD_tail = cgs 

   Pre-condition:  cD' |- cd 
                   cD', cd |- cD_tail

   Post-condition: cDg, cD_tail[ms'] |- cgs 
                   cDg = cD, cD_new where cD_new 
                   contains the new CVars (i.e. CtxVar, MVar, etc.) 
                   that were generated by splitting on cd 

*)
let genCGoals cD' cd cD_tail = 
  let LF.Decl (n, mtyp, dep) = cd in  
    match mtyp with 
      | LF.CTyp _ -> 
	  let cgs = Cover.genContextGoals cD' cd in 
	    List.map (fun (cDg, Coverage.CovCtx cPhi, ms) ->
		    (* cDg |- ms : cD' *)
			let ms' = LF.MDot (LF.CObj (cPhi),  ms) in
			let k = List.length cD_tail in
			let (cD'', ms0) = Coverage.addToMCtx cDg (cD_tail, ms') in
			  (* cDg, cD_tail |- ms0 : cD', cD_tail *)
			  (cD'' , Coverage.CovCtx (Whnf.cnormDCtx (cPhi, LF.MShift k)),  ms0 )
                     ) cgs  

  | _         -> 
      let cgs, _ = Cover.genCGoals cD' cd in 
	List.map (fun (cDg', cg, ms) ->
		    let Cover.CovGoal (cPsi', tR, sA') = cg in
		    (* let _ = Printf.printf "\n[Generated CovGoal] %s\n %s\n" 
		      (P.mctxToString cDg') (Cover.covGoalToString cDg' cg); Format.flush_str_formatter () in  *)
		    let ms' = LF.MDot (LF.ClObj ( Context.dctxToHat cPsi' , LF.MObj tR),  ms) in
		    let k   = List.length cD_tail in
		    let (cD'', ms0) = Coverage.addToMCtx cDg' (cD_tail, ms') in
		    let cg' = Coverage.CovGoal (Whnf.cnormDCtx (cPsi', LF.MShift k) ,
				       Whnf.cnorm (tR, LF.MShift k) ,
				       (Whnf.cnormTyp (Whnf.normTyp sA' , LF.MShift k), S.LF.id)) in
(*		    let _ = Printf.printf "\n[Generated CovGoal – shifted] k = %s\n cD'' = %s\n %s\n" 
(string_of_int k) (P.mctxToString cD'') (Cover.covGoalToString cD'' cg'); Format.flush_str_formatter () in *)
		       (cD'' , cg',  ms0 )
		 ) cgs

(* split : String -> int -> Comp.exp_chk  option *)
let split e i =
  let (loc, cD0, cG0, tau_theta) = Holes.getOneHole i in
  let tau0 = Whnf.cnormCTyp tau_theta in 

  let rec searchGctx i = function
  | LF.Empty -> None
  | LF.Dec (cG', Comp.CTypDecl (n, tau)) ->
    if (Id.string_of_name n) = e then
      let rec matchTyp tau =
        match tau with
        | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA, cPsi)) -> (* tA:typ, cPsi: dctx *)
          let cgs = Cover.genPatCGoals cD0 (compgctxTogctx cG0) tau [] in
          let bl = branchCovGoals loc 0 cG0 tau0 cgs in
            Some (matchFromPatterns l  (Comp.Var(l, i)) bl)
        | Comp.TypBase (l, c, mS) ->  (* c: cid_comp_typ , mS: meta_spine *)
            let cgs = Cover.genPatCGoals cD0 (compgctxTogctx cG0) tau [] in
            let bl = branchCovGoals loc 0 cG0 tau0 cgs in
            Some (matchFromPatterns l (Comp.Var(l, i)) bl)
        | Comp.TypClo (tau, t) -> matchTyp (Whnf.cnormCTyp (tau, t))
        | _ ->
          failwith ("Found variable in gCtx, cannot split on "^(Id.string_of_name n))
      in matchTyp tau
      else
        searchGctx (i+1) cG'
  in
  let rec searchMctx i cD (cD_tail : LF.ctyp_decl list) = match cD with 
    | LF.Empty -> None
    | LF.Dec (cD', cd) ->
	let LF.Decl (n, mtyp, dep) = cd in 
	if (Id.string_of_name n) = e then
	  let cgs   = genCGoals cD' cd cD_tail in
	  let bl    = branchCovGoals loc i cG0 tau0 cgs in
	  let mtyp' = Whnf.cnormMTyp (mtyp, LF.MShift i) in  (* cD0 |- mtyp' *)
	  let m0    =  (match  mtyp with
	     | LF.CTyp _ -> (Loc.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset i)))
	     | LF.ClTyp (LF.MTyp _ , cPsi ) ->
		    let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
		    let phat = dctxToHat cPsi' in
		      (Loc.ghost,
		       LF.ClObj (phat,LF.
				   MObj (LF.Root (Loc.ghost,
						  LF.MVar (LF.Offset i, LF.Shift 0),
						  LF.Nil)))) 
	     | LF.ClTyp (LF.PTyp _ , cPsi) ->
		    let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
		    let phat  = dctxToHat cPsi' in
		     (Loc.ghost, LF.ClObj (phat, LF.MObj (LF.Root (Loc.ghost , LF.PVar (i, LF.Shift 0), LF.Nil))))
	     | _ -> failwith "Interactive Splitting on Substitution Variables not supported")
	  in
	  let entry = Comp.Ann (Comp.Box (Loc.ghost, m0),
				Comp.TypBox(Loc.ghost, mtyp')) in
	    Some (matchFromPatterns (Loc.ghost) entry bl)

	else
	    searchMctx (i+1) cD' (cd::cD_tail)


  in
    match searchGctx 1 cG0 with
      | None ->
	  (match searchMctx 1 cD0 [] with
	     | None -> None
	     | Some s -> Some s)
      | Some s -> Some s

let whale () = Format.printf
";,,,,,,,,,,,,,,,,,'+++++++++++:,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,,,:#'........```.,'#+;,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,,+'..............````.'#',,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,,+,...................```.'+;,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,+:........................``,+',,,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,,+.............................,+;,,,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,+................................:++,,,,,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#...................................'++;,,,,,,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#......................................,'+++;,,,,,,,,,,,,,,,,`@\n\
;,,,,,,,,,,#...........................................,;++++':,,,,,,,,,`@\n\
;,,,,,,,,,,#..................................................,;+++#+'::`@\n\
;,,,,,,,,,,#......................................................```.,;`@\n\
;,,,,,,,,,,+..........................................................`` @\n\
;,,,,,,,,,,#............................................................@\n\
;,,,,,,,,,,+............................................................@\n\
;,,,,,,,,,#.............................................................@\n\
;,,,,,,,,+''#######+;...................#'.............................@\n\
;,,,,,,,,#,..........+#,................##'.............................@\n\
;,,,,,,,,#.............;#'..............................................@\n\
;,,,,,,,,:'...............'+##+'........................................@\n\
;,,,,,,,,,+,............................................................@\n\
;,,,,,,,,,,#............................................................@\n\
;,,``,,,,,,::....,,...........`.`........`........`.......``.......``...@\n\
;`....`,,,.....`........`...``...``..``....`..``....`...`....`...`....`.@\n\
``````````````;;.`````````````.;;```````````````````````````````````````@\n\
``````````````;;.`````````````.;;```````````````````````````````````````@\n\
``````````````;;..:.````.::```.;;``,,``,,```,:`.,.``,::,````````````````@\n\
``````````````;;;;;;:``;;;;;.`.;;`.;;``;;``;;;;;;.`:;;;;;```````````````@\n\
``````````````;;;``;;`,;:``;;``;;`.;;``;;``;;``;;.`````;;```````````````@\n\
``````````````;;.``;;`;;;;;;;``;;`.;;``;;`.;;``;;.`.;;;;;.``````````````@\n\
``````````````;;,``;;`;;.``````;;`.;;``;;`.;;``;;.`;;``;;.``````````````@\n\
``````````````;;;.;;;`:;;``.:``;;``;;,;;;``;;;;;;.`;;`.;;.``````````````@\n\
``````````````;;;;;;```;;;;;;``;;``:;;;;;``.;;;;;.`;;;;;;.``````````````@\n\
%s`;;@\n\
%s;;;;;,@\n"
("                                              ")
("                                           ")
