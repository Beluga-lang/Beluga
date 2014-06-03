(* module Interactive *)

module P = Pretty.Int.DefaultPrinter
module Loc = Camlp4.PreCast.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp
module Cover = Coverage
module S = Substitution
open Syntax.Int.Comp

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
| _ -> failwith "insertIMSub removed more than the sub could take"

let nameString n = n.Id.string_of_name

let nameOfLFcTypDecl = (function
| LF.Decl(n, _) -> n
| LF.DeclOpt n -> n)

let cvarOfLFcTypDecl td =
 match td with
| LF.Decl(n, LF.MTyp _) -> Store.CVar.MV n
| LF.Decl(n, LF.PTyp _) -> Store.CVar.PV ( Id.mk_name (Id.PVarName (Some (fun () -> (nameString n)))))
| LF.Decl(n, LF.STyp _) -> Store.CVar.SV n
| LF.Decl(n, LF.CTyp _) -> Store.CVar.CV n
| LF.DeclOpt(n) -> Store.CVar.MV n

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
      "["^P.dctxToString cD cPsi ^ " . " ^
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
let branchCovGoals loc i cG0 tA cgs =
  List.map (fun (cD,cg, ms) ->  match cg with
  | Cover.CovGoal(cPsi, tR, sA) ->
      let loc' = nextLoc loc in
       let ms = (if i = 0 then ms else insertIMSub i (LF.MObj(Context.dctxToHat cPsi, tR)) ms) in
      Printf.printf "CovGoal: %s \n"  (P.msubToString cD ms);
   Holes.collect(loc', cD, Whnf.cnormCtx(cG0, ms) , Whnf.cwhnfCTyp (Whnf.cnormCTyp tA, ms));
       let patt = PatMetaObj ( Loc.ghost, MetaObjAnn (Loc.ghost, cPsi, tR)) in
       Comp.Branch(Loc.ghost, cD, LF.Empty, patt, ms,Comp.Hole (loc', (fun () -> Holes.getHoleNum loc')))
(*      Comp.BranchBox (LF.Empty,cD, (cPsi , Comp.NormalPattern (tR, Comp.Hole (loc', (fun () -> Holes.getHoleNum loc'))), ms, LF.CShift 0)) (* random csub... *)  BranchBox is deprecated*)
  | Cover.CovPatt (cG, patt, (_tA',ms')) ->
      let loc' = nextLoc loc in
      Printf.printf "CovPat %s \n" (P.msubToString cD ms);
      Holes.collect(loc', cD, gctxToCompgctx cG, Whnf.cwhnfCTyp (Whnf.cnormCTyp tA, ms));
      Comp.Branch(Loc.ghost, cD, gctxToCompgctx cG , patt, ms, Comp.Hole (loc', (fun () -> Holes.getHoleNum loc')))
        ) cgs

let matchFromPatterns l e bl =
   Comp.Case(l, Pragma.RegularCase, e, bl)






let genVarName tA =
match Store.Cid.Typ.gen_var_name tA with
         | Some vGen -> Some (fun () -> String.lowercase (vGen ()))
         | None -> None




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
 | Fun (l, n, ec) ->
    let ec' =  mapHoleChk f ec in
    Fun(l, n, ec')
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
    let entries = !Store.Cid.Comp.entry_list in
    try
      let (cid_prog,loc') =  List.find (fun (_,loc') -> Holes.locWithin loc' loc) entries  in
      (Store.Cid.Comp.get cid_prog, loc')
    with Not_found -> failwith "Error in Interactive.funOfHole" in

  let (entry, loc) = funOfHole i in
  let Some lh = Holes.getHolePos i in
  (match entry.Store.Cid.Comp.prog with
  | Synint.Comp.RecValue (prog, ec, ms, env) ->
      let ec' = (mapHoleChk (ithHoler lh exp) ec) in
      let _l = Store.Cid.Comp.add loc
          (fun cid ->
            Store.Cid.Comp.mk_entry entry.Store.Cid.Comp.name entry.Store.Cid.Comp.typ entry.Store.Cid.Comp.implicit_arguments
              (Synint.Comp.RecValue (cid, ec', ms, env))
              entry.Store.Cid.Comp.mut_rec) in
      P.ppr_sgn_decl (Synint.Sgn.Rec(prog,entry.Store.Cid.Comp.typ ,ec'))
  | _ -> Holes.stashHoles (); failwith ("Error in replaceHole: "^(entry.Store.Cid.Comp.name.Id.string_of_name)^" is not a function\n")  )





(*********************)
(* top level tactics *)
(*********************)




(* intro: int -> Comp.exp_chk option *)
let  intro i =
  let used = ref false in
  let (loc, cDT, cGT, (tau, mS)) = Holes.getOneHole i in
  let rec crawl cD cG  = (function
 | Comp.TypArr (t1,t2) ->
     ( match t1 with
     | Comp.TypBox (l,tA,psi) ->
         used := true;
         let nam = Id.mk_name (Id.BVarName (genVarName tA)) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fun(l, nam, exp))
     | Comp.TypParam (l,tA,psi) ->
         used := true;
         let nam = Id.mk_name (Id.PVarName (genVarName tA)) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fun(l, nam, exp))
     | _ ->
         used := true;
         let nam = Id.mk_name (Id.NoName) in
         let Some exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1))) t2  in
         Some (Comp.Fun(Loc.ghost, nam, exp))
           )
 | Comp.TypPiBox (tdec, t') ->
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


(* idea: merge consecutive splits (on newly introduced variables) together (to pattern match deeper). *)
(* split : String -> int -> Comp.exp_chk  option *)
let split e i =
  let (loc, cD0, cG0, tH) = Holes.getOneHole i in
  let rec searchGctx i = function
  | LF.Empty -> None
  | LF.Dec (cG', Comp.CTypDecl (n, tau)) ->
      if (nameString n) = e then
        (match tau with
        | Comp.TypBox (l, tA, cPsi) -> (* tA:typ, cPsi: dctx *)
            let cgs = Cover.genPatCGoals cD0 (compgctxTogctx cG0) tau [] in
            let bl = branchCovGoals loc 0 cG0 tH cgs in
            Some (matchFromPatterns l  (Comp.Var i) bl)
        | Comp.TypBase (l, c, mS) ->  (* c: cid_comp_typ , mS: meta_spine *)
            let cgs = Cover.genPatCGoals cD0 (compgctxTogctx cG0) tau [] in
            let bl = branchCovGoals loc 0 cG0 tH cgs in
            Some (matchFromPatterns l (Comp.Var i) bl)
        | _ ->
            failwith ("Found variable in gCtx, cannot split on "^(nameString n)))
      else
        searchGctx (i+1) cG'
  in
let rec searchMctx i = function
  | LF.Empty ->
      None
  | LF.Dec (cD', ctypDecl) ->
      let LF.Decl(n, ctyp) = ctypDecl in
     (match ctyp with
      | LF.CTyp(_, _) ->
          (if (nameString n) = e then
            failwith ("Found variable in mCtx, cannot split on "^(nameString n)) (* could create a ctype wrapper, and split on it *)
          else
              searchMctx (i+1) cD' )
      | LF.MTyp (tA,cPsi, _) ->
          (if (nameString n) = e then
             let cgs = Cover.genCovGoals ((dropIMCtx i cD0),cPsi,tA) in
             let bl = branchCovGoals loc i cG0 tH cgs in
             let (vPsi, vOff) = dctxToHat cPsi in
             let entry = Comp.Ann ( Comp.Box(Loc.ghost, Comp.MetaObj(Loc.ghost, (vPsi,vOff) , LF.Root (Loc.ghost , LF.MVar (LF.Offset i, LF.Shift  vOff), LF.Nil))), Comp.TypBox(Loc.ghost, tA,cPsi)) in
            Some (matchFromPatterns (Loc.ghost) entry bl)
          else
            searchMctx (i+1) cD')
      | LF.PTyp (tA,cPsi, _ ) ->
          (if (nameString n) = e then
            let cgs = Cover.genCovGoals (cD',cPsi,tA) in
            let bl = branchCovGoals loc i cG0 tH cgs in
             let (vPsi, vOff) = dctxToHat cPsi in
             let entry = Comp.Ann ( Comp.Box(Loc.ghost, Comp.MetaObj(Loc.ghost, (vPsi,vOff) , LF.Root (Loc.ghost , LF.PVar (LF.Offset i, LF.Shift vOff), LF.Nil))), Comp.TypBox(Loc.ghost, tA,cPsi)) in
            Some (matchFromPatterns (Loc.ghost) entry bl)
          else
            searchMctx (i+1) cD')
      | _ -> searchMctx (i+1) cD')
  in
  match searchGctx 1 cG0 with
  | None ->
     (match searchMctx 1 cD0 with
      | None -> None
      | Some s -> Some s)
  | Some s -> Some s
