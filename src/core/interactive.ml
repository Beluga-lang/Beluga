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
  | (x,tau,tag) :: cG ->
      LF.Dec(gctxToCompgctx cG, Comp.CTypDecl (x, tau,tag))

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
  | CTypDecl (n, _, _) -> n
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
| LF.Dec (ccG', Comp.CTypDecl (x,tau, tag)) ->
    let cG' = compgctxTogctx ccG' in
    (x,tau,tag)::cG'

(* loc -> (LF.mctx * cov_goal * LF.msub) list -> (Comp.typ x LF.msub) -> Comp.branch list *)
(*  branchCovGoals loc n cG0 tA cgs =
    cD', cD0 |- tA with |cD0| = n
    for all (cD_i , cg_i, ms_i)  in cg,
      cD_i |- ms_i : cD'
*)
let branchCovGoals i cG0 tau cgs =
  let f = fun (cD, cg, ms) ->
    let make_branch patt =
      Comp.Branch
        ( Loc.ghost
        , cD
        , LF.Empty
        , patt
        , ms
        , Comp.Hole (Loc.ghost, None)
        )
    in
    match cg with
    | Cover.CovCtx cPsi ->
       (* Printf.printf "CovGoal %s with msub =  %s and i = %s\n"  (P.dctxToString cD cPsi) (P.msubToString cD ms) (string_of_int i); *)
       make_branch
         ( PatMetaObj
             ( Loc.ghost,
               ( Loc.ghost,
                 LF.CObj cPsi
               )
             )
         )

    | Cover.CovGoal(cPsi, tR, _tau' ) ->
       (* Printf.printf "CovGoal: %s \n"  (P.msubToString cD ms); flush stderr; *)
       (* _tau'  = tau[ms] *)
      make_branch
        (PatMetaObj
           ( Loc.ghost,
             ( Loc.ghost,
               LF.ClObj
                 ( Context.dctxToHat cPsi,
                   LF.MObj tR
                 )
             )
           )
        )

    | Cover.CovPatt (cG, patt, (_tau',ms')) ->
       (* Printf.printf "CovPat %s \n" (P.msubToString cD ms); *)
       make_branch patt
    | _ ->
       failwith "unable to handle coverage goal"
  in
  List.map f cgs

let matchFromPatterns l e bl =
   Comp.Case(l, Pragma.RegularCase, e, bl)

let genVarName tA = Store.Cid.Typ.gen_var_name tA

(** Traverses a computation-level type-checkable expression and
 * applies the given function to all holes. *)
let rec mapHoleChk f = function
 | Hole (l, name) -> f name l
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
let replaceHole (s : Holes.lookup_strategy) exp =
  let (i, h) =
    match Holes.get s with
    | None -> failwith "no such hole"
    | Some p -> p in

  let is = Holes.string_of_hole_id i in
(* test if Hole(l',f) is the ith hole, in which case
* detroy previous hole, commit staged holes and return the expression
* otherwise (not ith) returns back Hole(l',f)
* IMPORTANT: Check.comp.check that exp fits the holes beforehand *)
  let ithHoler l exp name l' =
    if (l = l') then
      begin
        Holes.destroy_holes_within l;
        exp
      end
    else
      Comp.Hole (l', name) in

  (* Figures out which function contains hole i. *)
  let funOfHole i =
    let entries = DynArray.to_list Store.Cid.Comp.entry_list in
    let opt =
      List.fold_left (fun found_opt entries' ->
        match found_opt with
        | None ->
           begin
             try
               let _entries = !entries' in
               let isWithin = fun (_, loc') -> Holes.loc_within loc' h.Holes.loc in
               (* Loop over the entries to find the one that contains the loc of the hole *)
               Some (List.find isWithin _entries)
               (* List.find raises if it can't find, so we catch and keep looking *)
             with
               _ -> None
           end
        | Some _ -> found_opt) None entries in
    match opt with
    | Some (cid_prog, loc') -> (Store.Cid.Comp.get cid_prog, loc')
    | _ -> failwith ("Error in Interactive.funOfHole: could not find function containing hole " ^ is) in

  (* Now we can actually find the function that contains the ith hole. *)
  let (entry, loc) = funOfHole i in

  (* We only allow replacing holes inside *functions*, so we check
   * that indeed this is a function (a recursive value) *)
  match entry.Store.Cid.Comp.prog with
  | Synint.Comp.RecValue (prog, ec, ms, env) ->
     (* Then, we can perform the replacement using ithHoler, which
      * traverses the expression and replaces the ith hole with the
      * given expression *)
     let ec' = (mapHoleChk (ithHoler (h.Holes.loc) exp) ec) in
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
  | _ ->
     failwith ("Error in replaceHole: "^(Id.string_of_name entry.Store.Cid.Comp.name)^" is not a function\n")

(*********************)
(* top level tactics *)
(*********************)

let is_inferred decl =
  not (LF.is_explicit decl)

let intro1 (h : Holes.hole) =
  let { Holes.loc
      ; Holes.name
      ; Holes.cD = cD
      ; Holes.info =
          Holes.CompHoleInfo
            { Holes.cG = cG
            ; Holes.compGoal = (tau, mS)
            }
      } = h
  in
  let new_hole = Comp.Hole (Loc.ghost, None) in
  let gen_var_for_typ =
    function
    | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA, psi)) ->
       Id.mk_name (Id.BVarName (genVarName tA))
    | Comp.TypBox (l, LF.ClTyp (LF.PTyp tA, psi)) ->
       Id.mk_name (Id.PVarName (genVarName tA))
    | _ ->
       Id.mk_name Id.NoName
  in
  (* We can only introduce an argument if the goal type of the hole is
  a (dependent) function space *)
  match tau with
  | Comp.TypArr (t1, t2) ->
     let v = gen_var_for_typ t1 in
     Comp.Fn (Loc.ghost, v, new_hole)
  | Comp.TypPiBox (tdec, t') when not (is_inferred tdec) ->
     let name = nameOfLFcTypDecl tdec in
     Comp.MLam (Loc.ghost, name, new_hole)
  (* Otherwise, we simply reconstruct the original hole. *)
  | t ->
     Comp.Hole (loc, Holes.option_of_name name)

(* intro: int -> Comp.exp_chk option *)
let intro (h : Holes.hole) =
  let { Holes.loc
      ; Holes.name
      ; Holes.cD = cDT
      ; Holes.info =
          Holes.CompHoleInfo
            { Holes.cG = cGT
            ; Holes.compGoal = (tau, mS)
            }
      } = h
  in
  let rec crawl cD cG =
    function
    | Comp.TypArr (t1,t2) ->
       begin
         match t1 with
         | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA, psi)) ->
            let nam = Id.mk_name (Id.BVarName (genVarName tA)) in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2  in
            Comp.Fn(l, nam, exp)
         | Comp.TypBox (l, LF.ClTyp (LF.PTyp tA,psi)) ->
            let nam = Id.mk_name (Id.PVarName (genVarName tA)) in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2 in
            Comp.Fn(l, nam, exp)
         | _ ->
            let nam = Id.mk_name (Id.NoName) in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2  in
            Comp.Fn(Loc.ghost, nam, exp)
       end
    | Comp.TypPiBox (tdec, t') when not (is_inferred tdec) ->
       let nam = nameOfLFcTypDecl tdec in
       let exp = crawl (LF.Dec (cD, tdec)) cG t' in
       Comp.MLam (Loc.ghost, nam , exp)
    | t ->
       Comp.Hole (Loc.ghost, None)
  in
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

(* split : String -> Holes.look -> Comp.exp_chk  option *)
let split (e : string) (hi : Holes.hole_id * Holes.hole) : Comp.exp_chk option =
  let ( hole_id,
        { Holes.loc
        ; Holes.name
        ; Holes.cD = cD0
        ; Holes.info =
            Holes.CompHoleInfo
              { Holes.cG = cG0
              ; Holes.compGoal = tau_theta
              }
        }
      ) = hi in

  let tau0 = Whnf.cnormCTyp tau_theta in 

  let rec searchGctx i =
    function
    | LF.Empty ->
       None
    | LF.Dec (cG', Comp.CTypDecl (n, tau, _)) ->
       if (Id.string_of_name n) = e then
         let rec matchTyp tau =
           match tau with
           | Comp.TypBox (l, _)
           | Comp.TypBase (l, _, _) -> (* tA:typ, cPsi: dctx *)
              let cgs = Cover.genPatCGoals cD0 (compgctxTogctx cG0) tau [] in
              let bl = branchCovGoals 0 cG0 tau0 cgs in
              Some (matchFromPatterns l (Comp.Var(l, i)) bl)
           | Comp.TypClo (tau, t) -> matchTyp (Whnf.cnormCTyp (tau, t))
             (* if the type is the type of a variable we're doing
               induction on, then we can just match the inner type
              *)
           | Comp.TypInd tau -> matchTyp tau
           | _ ->
              failwith
                ( "Found variable in gCtx, cannot split on "
                  ^ Id.string_of_name n )
         in
         matchTyp tau
       else
         searchGctx (i+1) cG'
    | _ ->
       failwith "gCtx contains something we can't split on"
  in
  let rec searchMctx i cD (cD_tail : LF.ctyp_decl list) =
    match cD with
    | LF.Empty -> None
    | LF.Dec (cD', (LF.Decl (n, mtyp, dep) as cd)) ->
	     if (Id.string_of_name n) = e then
	       let cgs = genCGoals cD' cd cD_tail in
	       let bl  = branchCovGoals i cG0 tau0 cgs in
	       let mtyp' = Whnf.cnormMTyp (mtyp, LF.MShift i) in  (* cD0 |- mtyp' *)
	       let m0  =
           match  mtyp with
	         | LF.CTyp _ -> (Loc.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset i)))
	         | LF.ClTyp (LF.MTyp _ , cPsi ) ->
		          let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
		          let phat = dctxToHat cPsi' in
		          ( Loc.ghost,
		            LF.ClObj
                  ( phat,
                    LF.MObj
                      (LF.Root
                         ( Loc.ghost,
					                 LF.MVar (LF.Offset i, LF.Shift 0),
					                 LF.Nil
                         )
                      )
                  )
              )
	         | LF.ClTyp (LF.PTyp _ , cPsi) ->
		          let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
		          let phat  = dctxToHat cPsi' in
		          ( Loc.ghost,
                LF.ClObj
                  ( phat,
                    LF.MObj
                      (LF.Root
                         ( Loc.ghost,
                           LF.PVar (i, LF.Shift 0),
                           LF.Nil
                         )
                      )
                  )
              )
	         | _ -> failwith "Interactive Splitting on Substitution Variables not supported"
	       in
	       let entry =
           Comp.Ann
             ( Comp.Box (Loc.ghost, m0),
               Comp.TypBox(Loc.ghost, mtyp')
             )
         in
	       Some (matchFromPatterns (Loc.ghost) entry bl)
	     else
	       searchMctx (i+1) cD' (cd::cD_tail)
    | _ ->
       failwith "mCtx contains something we can't split on"
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
