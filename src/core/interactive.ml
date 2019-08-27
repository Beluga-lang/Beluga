(* module Interactive *)

open Support

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module ExtComp = Syntax.Ext.Comp
module Comp = Syntax.Int.Comp
module Cover = Coverage
module S = Substitution
open Syntax.Int.Comp

let dprintf, dprint, _ = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

(*********************)
(* helper functions *)
(*********************)

let elaborate_exp (cD : LF.mctx) (cG : Comp.gctx)
      (t : ExtComp.exp_chk) (tp : Comp.typ * LF.msub)
    : Comp.exp_chk =
  dprintf
    begin fun p ->
    p.fmt "[elaborate_exp] @[<v>cD = %a@,cG = %a@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) cG
    end;
  let var_store = Store.Var.of_gctx cG in
  let cvar_store = Store.CVar.of_mctx cD in
  let t = Index.hexp cvar_store var_store t in
  Reconstruct.elExp cD cG t tp

let elaborate_exp' (cD : LF.mctx) (cG : Comp.gctx) (t : ExtComp.exp_syn)
    : Comp.exp_syn * Comp.tclo =
  dprintf
    begin fun p ->
    p.fmt "[elaborate_exp] @[<v>cD = %a@,cG = %a@]"
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) cG
    end;
  let var_store = Store.Var.of_gctx cG in
  let cvar_store = Store.CVar.of_mctx cD in
  let t = Index.hexp' cvar_store var_store t in
  Reconstruct.elExp' cD cG t


(* loc -> (LF.mctx * cov_goal * LF.msub) list -> (Comp.typ x LF.msub) -> Comp.branch list *)
(*  branchCovGoals loc n cG0 tA cgs =
    cD', cD0 |- tA with |cD0| = n
    for all (cD_i , cg_i, ms_i)  in cg,
      cD_i |- ms_i : cD'
*)
let branchCovGoals i cG0 cgs =
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
let replace_hole (i, h : Holes.hole_id * Holes.hole) exp =
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
      List.fold_left
        (fun found_opt entries' ->
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
          | Some _ -> found_opt)
        None
        entries
    in
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
     let _l =
       Store.Cid.Comp.add loc
         (fun cid ->
           Store.Cid.Comp.mk_entry
	           entry.Store.Cid.Comp.name
	           entry.Store.Cid.Comp.typ
	           entry.Store.Cid.Comp.implicit_arguments
	           entry.Store.Cid.Comp.total
             (Synint.Comp.RecValue (cid, ec', ms, env))
             entry.Store.Cid.Comp.mut_rec)
     in
     let open Format in
     fprintf std_formatter "%a@?"
       P.fmt_ppr_sgn_decl (Synint.Sgn.Rec [(prog,entry.Store.Cid.Comp.typ ,ec')])
  | _ ->
     failwith ("Error in replace_hole: "^(Id.string_of_name entry.Store.Cid.Comp.name)^" is not a function\n")

(*********************)
(* top level tactics *)
(*********************)

let is_inferred decl =
  not (LF.is_explicit decl)

(* intro: int -> Comp.exp_chk option *)
let intro (h : Holes.hole) =
  let { Holes.loc
      ; Holes.name
      ; Holes.cD = cDT
      ; Holes.info =
          Holes.CompHoleInfo
            { Holes.cG = cGT
            ; Holes.compGoal = (tau, mS)
            ; _
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
       let nam = LF.name_of_ctyp_decl tdec in
       let exp = crawl (LF.Dec (cD, tdec)) cG t' in
       Comp.MLam (Loc.ghost, nam , exp)
    | t ->
       Comp.Hole (Loc.ghost, None)
  in
  crawl cDT cGT tau

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
     let cgs, _ = Cover.genCGoals cD' mtyp in
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
         (*        let _ = Printf.printf "\n[Generated CovGoal – shifted] k = %s\n cD'' = %s\n %s\n"
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
              ; _
              }
        }
      ) = hi in

  let rec searchGctx i =
    function
    | LF.Empty ->
       None
    | LF.Dec (cG', Comp.CTypDecl (n, tau, _))
      when Id.string_of_name n = e ->
       let rec matchTyp tau =
         match tau with
         | Comp.TypBox (l, _)
           | Comp.TypBase (l, _, _) -> (* tA:typ, cPsi: dctx *)
            let cgs = Cover.genPatCGoals cD0 (Cover.gctx_of_compgctx cG0) tau [] in
            let bl = branchCovGoals 0 cG0 cgs in
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
    | LF.Dec (cG', _) -> searchGctx (i+1) cG'
  in
  let rec searchMctx i cD (cD_tail : LF.ctyp_decl list) =
    match cD with
    | LF.Empty -> None
    | LF.Dec (cD', (LF.Decl (n, mtyp, dep) as cd)) ->
	     if (Id.string_of_name n) = e then
	       let cgs = genCGoals cD' cd cD_tail in
	       let bl  = branchCovGoals i cG0 cgs in
	       let mtyp' = Whnf.cnormMTyp (mtyp, LF.MShift i) in  (* cD0 |- mtyp' *)
	       let m0  =
           match  mtyp with
	         | LF.CTyp _ -> (Loc.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset i)))
	         | LF.ClTyp (LF.MTyp _ , cPsi ) ->
		          let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
		          let phat = Context.dctxToHat cPsi' in
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
		          let phat  = Context.dctxToHat cPsi' in
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
  Maybe.(lazy (searchGctx 1 cG0) <|> lazy (searchMctx 1 cD0 []))
  |> Lazy.force

let whale_str =
  "%,,,,,,,,,,,,,,,,,#++++++++++++#,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,,,,,:##=.......```===#+;,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,,,,+=................``=###,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,,,+=...................```.#+,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,,+:........................``#+#,,,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,,+............................==+#,,,,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,+................................=+++,,,,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,#..................................==+++,,,,,,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,#.....................................==+++++,,,,,,,,,,,,,,,,\n\
   %,,,,,,,,,,#.........................................===+++++++,,,,,,,,,\n\
   %,,,,,,,,,,#................................................===++++#++:,\n\
   %,,,,,,,,,,#.....................................................======;\n\
   %,,,,,,,,,,+...........................................................`\n\
   %,,,,,,,,,,#............................................................\n\
   %,,,,,,,,,,+............................................................\n\
   %,,,,,,,,,#.............................................................\n\
   %,,,,,,,,+#########+;...................#'..............................\n\
   %,,,,,,,,#=..........+#'................##'.............................\n\
   %,,,,,,,,#.............;#'..............................................\n\
   %,,,,,,,,:=...............#+##+'........................................\n\
   %,,,,,,,,,+=............................................................\n\
   %,,,,,,,,,,#............................................................\n\
   %,,``,,,,,,::....==...........`=`........`........`.......``.......``...\n\
   %`====`,,,=====`========`===``===``==``====`==``====`...`====`...`====`.\n\
   %=======================================================================\n\
   %\n\
   %             QQ               QQ                                       \n\
   %             QQ               QQ                                       \n\
   %             QQ               QQ                                       \n\
   %             QQQQQQ   QQQQQ   QQ  QQ  QQ  QQQQQQ   QQQQQ               \n\
   %             QQQ  QQ  Q   QQ  QQ  QQ  QQ  QQ  QQ      QQ               \n\
   %             QQ   QQ QQQQQQQ  QQ  QQ  QQ  QQ  QQ   QQQQQ               \n\
   %             QQ   QQ QQ       QQ  QQ  QQ  QQ  QQ  QQ  QQ               \n\
   %             QQQ QQQ  QQ      QQ  QQ QQQ  QQQQQQ  QQ  QQ               \n\
   %             QQQQQQ   QQQQQQ  QQ   QQQQQ   QQQQQ  QQQQQQ               \n\
   %                                              QQ                       \n\
   %                                           QQQQQ                       \n"

let whale =
  let open Format in
  let emit = fprintf str_formatter "%s" in
  let pass c = emit (String.make 1 c) in
  let full_block = "\xe2\x96\x88" in
  let light_shade = "\xe2\x96\x91" in
  let medium_shade = "\xe2\x96\x92" in
  let dark_shade = "\xe2\x96\x93" in
  let f = function
    | 'Q' | '#' | '+' | ';' | ':' -> emit full_block
    | ',' -> pass ' ' (* emit light_shade *)
    | '\'' -> emit light_shade
    | '.' -> emit dark_shade
    | '=' | '`' -> emit medium_shade
    | c -> pass c
  in
  String.iter f whale_str; flush_str_formatter ()
