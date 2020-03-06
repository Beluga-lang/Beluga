open Support.Equality
(* module Interactive *)

open Support

module F = Misc.Function
module P = Pretty.Int.DefaultPrinter
module PExt = Pretty.Ext.DefaultPrinter
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

(** Elaborates an external syntax type into internal syntax, with abstraction.
    The returned integer is the number of implicit parameters.

    WARNING: elaboration of types as implemented here, by design,
    allows access to implicit variables in the meta-context.
    This is so that types given in the `suffices` Harpoon command can
    access implicit variables.
 *)
let elaborate_typ (cD : LF.mctx) (tau : ExtComp.typ) : Comp.typ * int =
  dprintf
    begin fun p ->
    p.fmt "[elaborate_typ] @[<v>tau =@ @[%a@] (external)@,\
           cD = @[%a@]@]"
      PExt.(fmt_ppr_cmp_typ l0) tau
      (P.fmt_ppr_lf_mctx P.l0) cD
    end;
  let cvars =
    Store.CVar.of_mctx (fun _ -> `explicit) cD
  in
  Index.hcomptyp cvars tau
  |> Reconstruct.comptyp_cD cD
  |> Abstract.comptyp
  |> F.through (fun (tau, _) -> Check.Comp.checkTyp cD tau)

let elaborate_exp (cD : LF.mctx) (cG : Comp.gctx)
      (t : ExtComp.exp_chk) (tp : Comp.typ * LF.msub)
    : Comp.exp_chk =
  dprintf
    begin fun p ->
    p.fmt "[elaborate_exp] @[<v>e = @[%a@] (external)@,\
           cD = @[%a@]@,\
           cG = @[%a@]@]"
      PExt.(fmt_ppr_cmp_exp_chk l0) t
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) cG
    end;
  let var_store = Store.Var.of_gctx cG in
  let cvar_store = Store.CVar.of_mctx LF.Depend.to_plicity' cD in
  let t = Index.hexp cvar_store var_store t in
  Reconstruct.elExp cD cG t tp

let elaborate_exp' (cD : LF.mctx) (cG : Comp.gctx) (t : ExtComp.exp_syn)
    : Comp.exp_syn * Comp.tclo =
  dprintf
    begin fun p ->
    p.fmt "[elaborate_exp] @[<v>i = @[%a@] (external)@,\
           cD = @[%a@]@,\
           cG = @[%a@]@]"
      PExt.(fmt_ppr_cmp_exp_syn l0) t
      (P.fmt_ppr_lf_mctx P.l0) cD
      (P.fmt_ppr_cmp_gctx cD P.l0) cG
    end;
  let var_store = Store.Var.of_gctx cG in
  let cvar_store = Store.CVar.of_mctx LF.Depend.to_plicity' cD in
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
      let id = Holes.allocate () in
      Comp.Branch
        ( Loc.ghost
        , LF.Empty
        , (cD , LF.Empty)
        , patt
        , ms
        , Comp.Hole (Loc.ghost, id, HoleId.Anonymous)
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
   Comp.(Case(l, PragmaCase, e, bl))

let genVarName tA = Store.Cid.Typ.gen_var_name tA

(** Traverses a computation-level type-checkable expression and
 * applies the given function to all computational holes. *)
let rec mapHoleChk f = function
 | Hole (l, id, name) -> f name l
 | Syn (l, es) ->
     let es' = mapHoleSyn f es in
         Syn (l, es')
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
  | MApp (l, es, cM, cU, pl) ->
     let es' =  mapHoleSyn f es in
     MApp(l, es', cM, cU, pl)
  | PairVal(l, es1, es2) ->
      let es1' =  mapHoleSyn f es1 in
      let es2' = mapHoleSyn f es2 in
      PairVal(l, es1', es2')
  | e -> e
and mapHoleBranch f = function
  | Branch (l, cD, cG, p, mS, ec) ->
      let ec' =  mapHoleChk f ec  in
      Branch (l, cD, cG, p, mS, ec')

let mapHoleThm f = function
  | Program e -> Program (mapHoleChk f e)
  | Proof p -> Misc.not_implemented "mapHoleThm"

(*********************)
(* top level tactics *)
(*********************)

let is_inferred decl =
  not (LF.is_explicit decl)

(* intro: int -> Comp.exp_chk option *)
let intro (h : Holes.comp_hole_info Holes.hole) =
  let { Holes.loc
      ; Holes.name
      ; Holes.cD = cDT
      ; Holes.info =
          { Holes.cG = cGT
          ; Holes.compGoal = (tau, mS)
          ; _
          }
      } = h
  in
  let rec crawl cD cG =
    function
    | Comp.TypArr (_, t1, t2) ->
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
    | Comp.TypPiBox (_, tdec, t') when not (is_inferred tdec) ->
       let nam = LF.name_of_ctyp_decl tdec in
       let exp = crawl (LF.Dec (cD, tdec)) cG t' in
       Comp.MLam (Loc.ghost, nam , exp)
    | t ->
       let id = Holes.allocate () in
       Comp.Hole (Loc.ghost, id, HoleId.Anonymous)
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
let genCGoals cD' (LF.Decl (n, mtyp, dep)) cD_tail =
  match mtyp with
  | LF.CTyp _ ->
     let cgs = Cover.genContextGoals cD' (n, mtyp, dep) in
     List.map (fun (cDg, cPhi, ms) ->
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
let split (e : string) (hi : HoleId.t * Holes.comp_hole_info Holes.hole) : Comp.exp_chk option =
  let ( hole_id,
        { Holes.loc
        ; Holes.name
        ; Holes.cD = cD0
        ; Holes.info =
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
      when Misc.String.equals (Id.string_of_name n) e ->
       let rec matchTyp tau =
         match tau with
         | Comp.TypBox (l, _)
           | Comp.TypBase (l, _, _) -> (* tA:typ, cPsi: dctx *)
            let names =
              Context.(names_of_mctx cD0 @ names_of_gctx cG0)
            in
            let cgs =
              Cover.genPatCGoals names cD0 tau
              |> List.map
                   (Cover.(map_inside (fun (cG, pat, tau) -> CovPatt (cG, pat, tau))))
            in
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
	     if Misc.String.equals (Id.string_of_name n) e then
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
                         ( Loc.ghost
                         , LF.MVar (LF.Offset i, LF.Shift 0)
                         , LF.Nil
                         , `explicit
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
                         ( Loc.ghost
                         , LF.PVar (i, LF.Shift 0)
                         , LF.Nil
                         , `explicit
                         )
                      )
                  )
              )
	         | _ -> failwith "Interactive Splitting on Substitution Variables not supported"
	       in
	       let entry = Comp.AnnBox (m0, mtyp') in
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

let iterMctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list =
  let (_, sub) = tA in
  let rec aux acc c = function
    | LF.Empty -> acc
    | LF.Dec (cD', LF.Decl(n, LF.ClTyp (LF.MTyp tA', cPsi'), LF.No))
    | LF.Dec (cD', LF.Decl(n, LF.ClTyp (LF.PTyp tA', cPsi'), LF.No))->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        let tA' = Whnf.cnormTyp (tA', LF.MShift c) in
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', sub);
        aux (n::acc) (c+1) cD'
      with | _ -> aux acc (c+1) cD' end
    | LF.Dec (cD', _) -> aux acc (c + 1) cD'
  in aux [] 1 cD

let iterDctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list =
  let rec aux acc = function
    | LF.DDec(cPsi', LF.TypDecl(n, tA')) ->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', LF.EmptySub);
        aux (n::acc) cPsi'
      with | _ -> aux acc cPsi' end
    | LF.DDec(cPsi', _) -> aux acc cPsi'
    | _ -> acc
  in
    aux [] cPsi

let iterGctx (cD : LF.mctx) (cG : Comp.gctx) (ttau : Comp.tclo) : Id.name list =
  let rec aux acc = function
    | LF.Empty -> acc
    | LF.Dec (cG', Comp.CTypDecl(n, tau', _ )) ->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        Unify.StdTrail.unifyCompTyp cD ttau (tau', LF.MShift 0);
        aux (n::acc) cG'
      with | _ -> aux acc cG' end
    | LF.Dec (cG', _) -> aux acc cG'
  in aux [] cG

let thin_line =
  let replicate n c = String.init n (Misc.const c) in
  replicate 80 '_'
let thin_line ppf () = Format.fprintf ppf "%s" thin_line

let fmt_ppr_hole ppf (i, (Holes.Exists (w, h)) : HoleId.t * Holes.some_hole) : unit =
  let open Format in
  let { Holes.loc; Holes.name; Holes.cD; Holes.info } = h in
  (* First, we do some preparations. *)
  (* Normalize the LF and computational contexts as well as the goal type. *)
  let cD = Whnf.normMCtx cD in
  (* Now that we've prepped all the things to format, we can prepare the message. *)
  (* We do this by preparing different *message components* which are
   * assembled into the final message. *)

  fprintf ppf "@[<v>";

  (* 1. The 'hole identification component' contains the hole name (if any) and its number. *)
  fprintf ppf
    "@[<hov>%a:@ Hole number %a, %a@]@,  @[<v>"
    Loc.print loc
    HoleId.fmt_ppr_id i
    HoleId.fmt_ppr_name name;
  (* thin_line ppf (); *)

  (* 2. The meta-context information. *)
  fprintf ppf "Meta-context:@,  @[<v>%a@]@,"
    (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD;
  (* thin_line ppf (); *)

  let plural ppf = function
    | true -> fprintf ppf "s"
    | false -> ()
  in

  (* The remainder of the formatting hinges on whether we're printing
     an LF hole or a computational hole.
   *)
  begin match w, info with
  | Holes.LFInfo, { Holes.cPsi; Holes.lfGoal; Holes.lfSolution } ->
     let lfGoal' = Whnf.normTyp lfGoal in
     let cPsi = Whnf.normDCtx cPsi in

     (* 3. format the LF context information *)
     fprintf ppf "LF Context:@,  @[<v>%a@]@,"
       (P.fmt_ppr_lf_dctx cD P.l0) cPsi;

     (* 4. Format the goal. *)
     thin_line ppf ();
     fprintf ppf "@[Goal:@ @[%a@]@]" (P.fmt_ppr_lf_typ cD cPsi P.l0) lfGoal';

     begin match lfSolution with
     | None ->
        (* 5. The in-scope variables that have the goal type, if any *)
        let suggestions =
          (* Need to check both the LF context and the meta-variable context. *)
          iterMctx cD cPsi lfGoal @ iterDctx cD cPsi lfGoal
        in
        if Misc.List.nonempty suggestions then
          fprintf ppf
            "@,@[<hov 2>Variable%a of this type:@ @[<h>%a@]@]"
            plural (List.length suggestions = 1)
            (pp_print_list ~pp_sep: Fmt.comma Id.print) suggestions
     | Some sM ->
        fprintf ppf "@[<v 2>This hole is solved:@,@[%a@]@]"
          (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)
     end

  | Holes.CompInfo, { Holes.cG; Holes.compGoal = (tau, theta); Holes.compSolution } ->
     let cG = Whnf.normGCtx cG in
     let goal = Whnf.cnormCTyp (tau, theta) in
     (* 3. The (computational) context information. *)
     fprintf ppf "Computation context:@,  @[<v>%a@]@,"
       (P.fmt_ppr_cmp_gctx ~sep: pp_print_cut cD P.l0) cG;

     (* 4. The goal type, i.e. the type of the hole. *)
     fprintf ppf "@[<hov>Goal:@ %a@]"
       (P.fmt_ppr_cmp_typ cD P.l0) goal;

     begin match compSolution with
     | None ->
        (* Collect a list of variables that already have the goal type. *)
        let suggestions = iterGctx cD cG (tau, theta) in
        if Misc.List.nonempty suggestions then
          fprintf ppf
            "@,@,Variable%a of this type: @[<h>%a@]"
            plural (List.length suggestions = 1)
            (pp_print_list ~pp_sep: Fmt.comma Id.print) suggestions
     | Some e ->
        fprintf ppf "@[<v 2>This hole is solved:@,@[%a@]@]"
          (P.fmt_ppr_cmp_exp_chk cD cG P.l0) e
     end
  end;
  fprintf ppf "@]@]"
