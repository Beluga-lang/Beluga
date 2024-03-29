open Support.Equality
open Support
open Beluga_syntax

module F = Fun
module P = Prettyint.DefaultPrinter
module LF = Synint.LF
module ExtComp = Beluga_syntax.Ext.Comp
module Comp = Synint.Comp
module Cover = Coverage
module S = Substitution
open Synint.Comp

(*********************)
(* helper functions  *)
(*********************)

(* loc -> (LF.mctx * cov_goal * LF.msub) list -> (Comp.typ x LF.msub) -> Comp.branch list *)
(*  branchCovGoals loc n cG0 tA cgs =
    cD', cD0 |- tA with |cD0| = n
    for all (cD_i , cg_i, ms_i)  in cg,
      cD_i |- ms_i : cD'
 *)
let branchCovGoals i cG0 cgs =
  let f (cD, cg, ms) =
    let make_branch patt =
      let id = Holes.allocate () in
      Comp.Branch
        ( Location.ghost
        , LF.Empty
        , (cD, LF.Empty)
        , patt
        , ms
        , Comp.Hole (Location.ghost, id, HoleId.Anonymous)
        )
    in
    match cg with
    | Cover.CovCtx cPsi ->
       (* Printf.printf "CovGoal %s with msub =  %s and i = %s\n" (P.dctxToString cD cPsi) (P.msubToString cD ms) (string_of_int i); *)
       make_branch
         (PatMetaObj
            ( Location.ghost
            , ( Location.ghost
              , LF.CObj cPsi
              )
            )
         )

    | Cover.CovGoal (cPsi, tR, _) ->
       (* Printf.printf "CovGoal: %s \n" (P.msubToString cD ms); flush stderr; *)
       (* _tau' = tau[ms] *)
       make_branch
         (PatMetaObj
            ( Location.ghost
            , ( Location.ghost
              , LF.ClObj
                  ( Context.dctxToHat cPsi
                  , LF.MObj tR
                  )
              )
            )
         )

    | Cover.CovPatt (_, patt, _) ->
       (* Printf.printf "CovPat %s \n" (P.msubToString cD ms); *)
       make_branch patt
    | _ ->
       failwith "unable to handle coverage goal"
  in
  List.map f cgs

let matchFromPatterns l e bl =
   Comp.(Case (l, PragmaCase, e, bl))

let genVarName tA = Store.Cid.Typ.gen_var_name tA

(** Traverses a computation-level type-checkable expression and
    applies the given function to all computational holes. *)
let rec mapHoleExp f =
  function
  | Hole (l, id, name) -> f name l

  | Fn (l, n, ec) ->
     let ec' = mapHoleExp f ec in
     Fn (l, n, ec')

  | MLam (l, n, ec, p) ->
     let ec' = mapHoleExp f ec in
     MLam (l, n, ec', p)

  | Let (t, es, (n, ec)) ->
     let es' = mapHoleExp f es in
     let ec' = mapHoleExp f ec in
     Let (t, es', (n, ec'))

  | LetTuple (t, es, (ns, ec)) ->
     let es' = mapHoleExp f es in
     let ec' = mapHoleExp f ec in
     LetTuple (t, es', (ns, ec'))

  | Tuple (l, ecs) ->
     let ecs' = List2.map (mapHoleExp f) ecs in
     Tuple (l, ecs')

  | Case (l, s, es, bs) ->
     let es' = mapHoleExp f es in
     let bs' = List.map (mapHoleBranch f) bs in
     Case (l, s, es', bs')

  | Apply (l, es, ec) ->
     let es' = mapHoleExp f es in
     let ec' = mapHoleExp f ec in
     Apply (l, es', ec')

  | MApp (l, es, cM, cU, pl) ->
     let es' = mapHoleExp f es in
     MApp (l, es', cM, cU, pl)

  | e -> e

and mapHoleBranch f =
  function
  | Branch (l, cD, cG, p, mS, ec) ->
     let ec' = mapHoleExp f ec in
     Branch (l, cD, cG, p, mS, ec')

let mapHoleThm f =
  function
  | Program e -> Program (mapHoleExp f e)
  | Proof p -> Misc.not_implemented "mapHoleThm"

(*********************)
(* top level tactics *)
(*********************)

let is_inferred decl =
  Bool.not (LF.is_explicit decl)

let intro (h : Holes.comp_hole_info Holes.hole) =
  let { Holes.cD = cDT; Holes.info = { Holes.cG = cGT; Holes.compGoal = (tau, _); _ }; _ } =
    h
  in
  let rec crawl cD cG =
    function
    | Comp.TypArr (_, t1, t2) ->
       begin
         match t1 with
         | Comp.TypBox (l, LF.ClTyp (LF.MTyp tA, psi)) ->
            let nam = Name.mk_mvar_name (genVarName tA) in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2 in
            Comp.Fn(l, nam, exp)
         | Comp.TypBox (l, LF.ClTyp (LF.PTyp tA, psi)) ->
            let nam = Name.mk_pvar_name (genVarName tA) in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2 in
            Comp.Fn(l, nam, exp)
         | _ ->
            let nam = Name.mk_no_name () in
            let exp = crawl cD (LF.Dec (cG, Comp.CTypDecl (nam, t1, false))) t2 in
            Comp.Fn(Location.ghost, nam, exp)
       end
    | Comp.TypPiBox (_, tdec, t')
         when Bool.not (is_inferred tdec) ->
       let nam = LF.name_of_ctyp_decl tdec in
       let exp = crawl (LF.Dec (cD, tdec)) cG t' in
       Comp.MLam (Location.ghost, nam, exp, Plicity.explicit)
    | _ ->
       let id = Holes.allocate () in
       Comp.Hole (Location.ghost, id, HoleId.Anonymous)
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
let genCGoals cD' (LF.Decl { name =n; typ = mtyp; plicity; inductivity }) cD_tail =
  match mtyp with
  | LF.CTyp _ ->
     Cover.genContextGoals cD' (n, mtyp, plicity, inductivity)
     |> List.map
          begin fun (cDg, cPhi, ms) ->
          (* cDg |- ms : cD' *)
          let ms' = LF.MDot (LF.CObj (cPhi), ms) in
          let k = List.length cD_tail in
          let (cD'', ms0) = Coverage.addToMCtx cDg (cD_tail, ms') in
          (* cDg, cD_tail |- ms0 : cD', cD_tail *)
          (cD'', Coverage.CovCtx (Whnf.cnormDCtx (cPhi, LF.MShift k)), ms0)
          end

  | _ ->
     Cover.genCGoals cD' mtyp
     |> Pair.fst
     |> List.map
          begin fun (cDg', cg, ms) ->
          let Cover.CovGoal (cPsi', tR, sA') = cg in
          let ms' = LF.MDot (LF.ClObj (Context.dctxToHat cPsi', LF.MObj tR), ms) in
          let k = List.length cD_tail in
          let (cD'', ms0) = Coverage.addToMCtx cDg' (cD_tail, ms') in
          let cg' =
            Coverage.CovGoal
              ( Whnf.cnormDCtx (cPsi', LF.MShift k)
              , Whnf.cnorm (tR, LF.MShift k)
              , (Whnf.cnormTyp (Whnf.normTyp sA', LF.MShift k), S.LF.id)
              )
          in
          (cD'', cg', ms0)
          end

let split (e : string) (hi : HoleId.t * Holes.comp_hole_info Holes.hole) : Comp.exp option =
  let (_, { Holes.cD = cD0; Holes.info = { Holes.cG = cG0; _ }; _ }) =
    hi
  in

  let rec searchGctx i =
    function
    | LF.Empty -> None
    | LF.Dec (cG', Comp.CTypDecl (n, tau, _))
         when String.equal (Name.string_of_name n) e ->
       let rec matchTyp =
         function
         | Comp.TypBox (l, _)
           | Comp.TypBase (l, _, _) -> (* tA:typ, cPsi: dctx *)
            let names =
              Context.(names_of_mctx cD0 @ names_of_gctx cG0)
            in
            let cgs =
              Cover.(genPatCGoals names withPatVar cD0 tau)
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
                ^ Name.string_of_name n
              )
       in
       matchTyp tau
    | LF.Dec (cG', _) -> searchGctx (i + 1) cG'
  in
  let rec searchMctx i cD (cD_tail : LF.ctyp_decl list) =
    match cD with
    | LF.Empty -> None
    | LF.Dec (cD', (LF.Decl { name = n; typ = mtyp; _ } as cd)) ->
       if String.equal (Name.string_of_name n) e
       then
         begin
           let cgs = genCGoals cD' cd cD_tail in
           let bl = branchCovGoals i cG0 cgs in
           let mtyp' = Whnf.cnormMTyp (mtyp, LF.MShift i) in (* cD0 |- mtyp' *)
           let m0 =
             match mtyp with
             | LF.CTyp _ -> (Location.ghost, LF.CObj (LF.CtxVar (LF.CtxOffset i)))
             | LF.ClTyp (LF.MTyp _, cPsi) ->
                let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
                let phat = Context.dctxToHat cPsi' in
                ( Location.ghost,
                  LF.ClObj
                    ( phat,
                      LF.MObj
                        (LF.Root
                           ( Location.ghost
                           , LF.MVar (LF.Offset i, LF.Shift 0)
                           , LF.Nil
                           , Plicity.explicit
                           )
                        )
                    )
                )
             | LF.ClTyp (LF.PTyp _, cPsi) ->
                let cPsi' = Whnf.cnormDCtx (cPsi, LF.MShift i) in
                let phat = Context.dctxToHat cPsi' in
                ( Location.ghost
                , LF.ClObj
                    ( phat
                    , LF.MObj
                        (LF.Root
                           ( Location.ghost
                           , LF.PVar (i, LF.Shift 0)
                           , LF.Nil
                           , Plicity.explicit
                           )
                        )
                    )
                )
             | _ -> failwith "Interactive Splitting on Substitution Variables not supported"
           in
           let entry = Comp.AnnBox (Location.ghost, m0, mtyp') in
           Some (matchFromPatterns (Location.ghost) entry bl)
         end
       else
         searchMctx (i + 1) cD' (cd :: cD_tail)
    | _ ->
       failwith "mCtx contains something we can't split on"
  in
  Option.(lazy (searchGctx 1 cG0) <||> lazy (searchMctx 1 cD0 []))
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

let pp_whale ppf =
  let emit = Format.pp_print_string ppf in
  let pass = Format.pp_print_char ppf in
  let full_block = "\xe2\x96\x88" in
  let light_shade = "\xe2\x96\x91" in
  let medium_shade = "\xe2\x96\x92" in
  let dark_shade = "\xe2\x96\x93" in
  String.iter
    (function
      | 'Q' | '#' | '+' | ';' | ':' -> emit full_block
      | ',' -> pass ' ' (* emit light_shade *)
      | '\'' -> emit light_shade
      | '.' -> emit dark_shade
      | '=' | '`' -> emit medium_shade
      | c -> pass c)
    whale_str

let whale = Format.asprintf "%t" pp_whale

let iterMctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Name.t list =
  let (_, sub) = tA in
  let rec aux acc c =
    function
    | LF.Empty -> acc
    | LF.Dec (cD', LF.Decl { name = n; typ = LF.ClTyp (LF.MTyp tA', cPsi'); plicity = Plicity.Explicit; _ })
      | LF.Dec (cD', LF.Decl { name = n; typ = LF.ClTyp (LF.PTyp tA', cPsi'); plicity = Plicity.Explicit; _ }) ->
       begin
         try
           Unify.StdTrail.resetGlobalCnstrs ();
           let tA' = Whnf.cnormTyp (tA', LF.MShift c) in
           Unify.StdTrail.unifyTyp cD cPsi tA (tA', sub);
           aux (n :: acc) (c + 1) cD'
         with
         | _ -> aux acc (c + 1) cD'
       end
    | LF.Dec (cD', _) -> aux acc (c + 1) cD'
  in
  aux [] 1 cD

let iterDctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Name.t list =
  let rec aux acc =
    function
    | LF.DDec (cPsi', LF.TypDecl(n, tA')) ->
       begin
         try
           Unify.StdTrail.resetGlobalCnstrs ();
           Unify.StdTrail.unifyTyp cD cPsi tA (tA', LF.EmptySub);
           aux (n :: acc) cPsi'
         with
         | _ -> aux acc cPsi'
       end
    | LF.DDec (cPsi', _) -> aux acc cPsi'
    | _ -> acc
  in
  aux [] cPsi

let iterGctx (cD : LF.mctx) (cG : Comp.gctx) (ttau : Comp.tclo) : Name.t list =
  let rec aux acc =
    function
    | LF.Empty -> acc
    | LF.Dec (cG', Comp.CTypDecl(n, tau', _)) ->
       begin
         try
           Unify.StdTrail.resetGlobalCnstrs ();
           Unify.StdTrail.unifyCompTyp cD ttau (tau', LF.MShift 0);
           aux (n :: acc) cG'
         with
         | _ -> aux acc cG'
       end
    | LF.Dec (cG', _) -> aux acc cG'
  in
  aux [] cG

let thin_line =
  let replicate n c = String.init n (Fun.const c) in
  replicate 80 '_'

let thin_line ppf () = Format.fprintf ppf "%s" thin_line

let fmt_ppr_hole ppf (i, (Holes.Exists (w, h)) : HoleId.t * Holes.some_hole) : unit =
  let open Format in
  let { Holes.location; Holes.name; Holes.cD; Holes.info } = h in
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
    Location.print location
    HoleId.fmt_ppr_id i
    HoleId.fmt_ppr_name name;
  (* thin_line ppf (); *)

  (* 2. The meta-context information. *)
  fprintf ppf "Meta-context:@,  @[<v>%a@]@,"
    (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD;
  (* thin_line ppf (); *)

  let plural ppf =
    function
    | true -> fprintf ppf "s"
    | false -> ()
  in

  (* The remainder of the formatting hinges on whether we're printing
     an LF hole or a computational hole.
   *)
  begin match (w, info) with
  | (Holes.LFInfo, { Holes.cPsi; Holes.lfGoal; Holes.lfSolution }) ->
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
        if List.nonempty suggestions
        then
          fprintf ppf
            "@,@[<hov 2>Variable%a of this type:@ @[<h>%a@]@]"
            plural (List.length suggestions = 1)
            (pp_print_list ~pp_sep: Format.comma Name.pp) suggestions
     | Some sM ->
        fprintf ppf "@[<v 2>This hole is solved:@,@[%a@]@]"
          (P.fmt_ppr_lf_normal cD cPsi P.l0) (Whnf.norm sM)
     end

  | (Holes.CompInfo, { Holes.cG; Holes.compGoal = (tau, theta); Holes.compSolution }) ->
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
        if List.nonempty suggestions
        then
          fprintf ppf
            "@,@,Variable%a of this type: @[<h>%a@]"
            plural (List.length suggestions = 1)
            (pp_print_list ~pp_sep: Format.comma Name.pp) suggestions
     | Some e ->
        fprintf ppf "@[<v 2>This hole is solved:@,@[%a@]@]"
          (P.fmt_ppr_cmp_exp cD cG P.l0) e
     end
  end;
  fprintf ppf "@]@]"
