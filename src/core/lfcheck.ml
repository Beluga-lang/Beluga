module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [5])

  open Context
  open Store.Cid
  open Substitution
  open Syntax.Int.LF
  open Error

  module Print = Pretty.Int.DefaultPrinter

  module Unify = Unify.EmptyTrail

  exception Violation of string
  exception Error of Syntax.Loc.t option * error
  exception SpineMismatch




(* Seems broken Sat Sep  4 12:24:43 2010 -bp 
  (* ctxToSub cPsi:
   *
   * generates, based on cPsi, a substitution suitable for unification
   *
   * Currently broken: assumes all types in cPsi are atomic
   *)
  let rec ctxToSub cPsi = match cPsi with
    | Null -> LF.id
    | DDec (cPsi', TypDecl (_, tA)) ->
        let s = ((ctxToSub cPsi') : sub) in
          (* For the moment, assume tA atomic. *)
          (* lower tA? *)
          (* A = A_1 -> ... -> A_n -> P

             create cPhi = A_1, ..., A_n
             \x_1. ... \x_n. u[id]
             u::P[cPhi]

             already done in reconstruct.ml
             let (_, d) = Context.dctxToHat cPsi in
             let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in
             in elSpineIW
          *)
        let (_, phat') = Context.dctxToHat cPsi' in
        let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in
          (* let u = Whnf.newMVar (Null ,  TClo( tA, s)) in *)
        let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
          Dot (front, LF.comp s LF.shift)

*)
let rec ctxShift cPsi = begin match cPsi with
  | Null              -> Shift (NoCtxShift , 0 )
  | CtxVar psi        -> Shift (CtxShift psi, 0)
  | DDec   (cPsi, _x) -> 
      match  ctxShift cPsi with
          Shift (cshift, n)  -> Shift (cshift, n+1)
  end

  (* ctxToSub' cPhi cPsi = s 

     if x1:A1, ... xn:An = cPsi
     then D = u1:A1[cPhi], ... un:An[cPhi]

     s.t. D; cPhi |- u1[id]/x1 ... un[id]/xn : cPsi
  *)
  let rec ctxToSub' cPhi cPsi = match cPsi with
    | Null -> ctxShift cPhi (* LF.id *)
    | DDec (cPsi', TypDecl (_, tA)) ->
        let s = ((ctxToSub' cPhi cPsi') : sub) in
          (* For the moment, assume tA atomic. *)
          (* lower tA? *)
          (* A = A_1 -> ... -> A_n -> P

             create cPhi = A_1, ..., A_n
             \x_1. ... \x_n. u[id]
             u::P[cPhi]

             already done in reconstruct.ml
             let (_, d) = Context.dctxToHat cPsi in
             let tN     = etaExpandMV Int.LF.Null (tA, s) (Int.LF.Shift d) in
             in elSpineIW
          *)
        (* let (_, phat') = Context.dctxToHat cPsi' in*)
        (* let u     = Whnf.etaExpandMV Null (tA, s) (Shift (NoCtxShift, phat')) in *)

        (* let u     = Whnf.etaExpandMV Null (tA, s) LF.id in *)
          (* let u = Whnf.newMVar (Null ,  TClo( tA, s)) in *)
        (* let u     = Whnf.etaExpandMV cPhi (tA, LF.comp s (ctxShift cPhi)) LF.id in *)
	let u     = Whnf.etaExpandMV cPhi (tA, s) LF.id in 
        let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
          (* Dot (front, LF.comp s LF.shift)  *)
           Dot (front, s) 


  (* check cD cPsi (tM, s1) (tA, s2) = ()
   *
   * Invariant:
   *
   * If   ; cD ; cPsi |- s1 <= cPsi1
   * and  ; cD ; cPsi |- s2 <= cPsi2    cPsi2 |- tA <= type
   * returns ()
   * if there exists an tA' s.t.
   * ; cD ; cPsi1 |- tM      <= tA'
   * and  ; cD ; cPsi  |- tA'[s1]  = tA [s2] : type
   * and  ; cD ; cPsi  |- tM [s1] <= tA'[s1]
   * otherwise exception Error is raised
   *)
  let rec checkW cD cPsi sM sA = match (sM, sA) with
    | ((Lam (_, _, tM), s1),   (PiTyp ((TypDecl (_x, _tA) as tX, _), tB), s2)) -> 
        check cD
          (DDec (cPsi, LF.decSub tX s2))
          (tM, LF.dot1 s1)
          (tB, LF.dot1 s2)

    | ((Tuple (_, tuple), s1),   (Sigma typRec, s2)) -> 
        checkTuple cD cPsi (tuple, s1) (typRec, s2)

    | ((Root (loc, _h, _tS), _s (* id *)),   (Atom _, _s')) ->
        (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
          begin try
            let _ = dprint (fun () -> "[check] " ^ P.normalToString cD cPsi sM ^ 
                              " <= " ^ P.typToString cD cPsi sA ) in
            let sP = syn' cD cPsi sM in 
            let _ = dprint (fun () -> "[check] synthesized " ^ P.normalToString cD cPsi sM ^ 
                              " => " ^ P.typToString cD cPsi sP ) in
            let (tP', tQ') = (Whnf.normTyp sP , Whnf.normTyp sA) in 
              if not (Whnf.convTyp  (tP', LF.id) (tQ', LF.id)) then 
                (dprint (fun () -> "here!") ; 
                 raise (Error (loc, TypMismatch (cD, cPsi, sM, sA, sP))))
          with SpineMismatch ->
            raise (Error (loc, (IllTyped (cD, cPsi, sM, sA))))
          end

    | ((Lam (loc, _, _), _), _) ->
       raise (Error (loc, IllTyped (cD, cPsi, sM, sA)))

    | ((Root (loc, _, _), _), _) ->
       raise (Error (loc, IllTyped (cD, cPsi, sM, sA)))

  and check cD cPsi sM sA = checkW cD cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

  and checkTuple cD cPsi (tuple, s1) (typRec, s2) = match (tuple, typRec) with
    | (Last tM,   SigmaLast tA) ->
        checkW cD cPsi (tM, s1) (tA, s2)

    | (Cons (tM, restOfTuple),   SigmaElem (_x, tA, restOfTypRec)) ->
        checkW cD cPsi (tM, s1) (tA, s2)
      ; checkTuple cD cPsi
          (restOfTuple, s1)
          (restOfTypRec, Dot (Obj tM, s2))

    | (_, _) ->
        raise (Violation ("checkTuple arity mismatch"))


  and syn' cD cPsi (Root (loc, h, tS), s (* id *)) = 
    let sA' = Whnf.whnfTyp (inferHead loc cD cPsi h, LF.id) in
      synSpine cD cPsi (tS, s) sA'
        

  and syn cD cPsi ((Root (loc, _h, _tS), _s (* id *)) as sR) = 
    begin try
      syn' cD cPsi sR
    with SpineMismatch -> 
      raise (Error (loc, SpineIllTyped))
    end

  (* synSpine cD cPsi sS sA = sP
   * 
   * Invariant:
   *
   * ; cD ; cPsi sS : sA => sP
   *)
  and synSpine cD cPsi sS sA = match (sS, sA) with
    | ((Nil, _),   sP) ->
        sP
    
    | ((SClo (tS, s'), s),   sA) ->
        synSpine cD cPsi (tS, LF.comp s' s) sA
    
    | ((App (tM, tS), s1),   (PiTyp ((TypDecl (_, tA1), _), tB2), s2)) ->
        check cD cPsi (tM, s1) (tA1, s2);
        (*     cD ; cPsi1        |- tM  <= tA1'
         * and cD ; cPsi         |- s1  <= cPsi1
         * and cD ; cPsi2, x:tA1 |- tB2 <= type
         * and [s1]tA1' = [s2]tA1
         *)
        let tB2 = Whnf.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
          synSpine cD cPsi (tS, s1) tB2
    
    | ((App _, _),   (Atom _, _)) ->
        raise SpineMismatch

(* TODO: move this function somewhere else, and get rid of duplicate in reconstruct.ml  -jd 2009-03-14 *)

  (* inferHead loc cD cPsi h = tA
   *
   * Invariant:
   *
   * returns tA if
   * cD ; cPsi |- h => tA
   * where cD ; cPsi |- tA <= type
   * else exception Error is raised.
   *)
  and inferHead loc cD cPsi head = match head with
    | BVar k' ->
        let (_, _l) = dctxToHat cPsi in
        let TypDecl (_, tA) = ctxDec cPsi k' in
          tA
    
    | Proj (tuple_head, target) ->
        let srecA = match tuple_head with
          | BVar k' ->
              let TypDecl (_, Sigma recA) = ctxSigmaDec cPsi k' in
              let _ = dprint (fun () -> "[InferHead] " ^ P.dctxToString cD cPsi) in
              let _ = dprint (fun () -> "|-  " ^  P.headToString cD cPsi head ^ "\n" ^ 
                                " where " ^ P.headToString cD cPsi tuple_head ^ 
				" has type " ^ P.typRecToString cD cPsi (recA, LF.id)) in
                (recA, LF.id)
          | PVar (Offset p, s) ->
              let (_, Sigma recA, cPsi') = Whnf.mctxPDec cD p in
                checkSub loc cD cPsi s cPsi';
                (recA, s)
        in
        let (_tA, s) as sA = getType tuple_head srecA target 1 in 
          dprint (fun () -> "getType (" ^ P.headToString cD cPsi head ^ ") = " ^ P.typToString cD cPsi sA);
          dprint (fun () -> "s = " ^ P.subToString cD cPsi s);
          TClo sA

    
    | Const c ->
        (Term.get c).Term.typ
    
    | MVar (Offset u, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (_, tA, cPsi') = Whnf.mctxMDec cD u in
        let _ = dprint (fun () -> "[inferHead] " ^ P.headToString cD cPsi head ) in 
        let _ = dprint (fun () -> "[inferHead] " ^ P.dctxToString cD cPsi ^ "   |-   " ^ 
                          P.subToString cD cPsi s ^ " <= " ^ P.dctxToString cD cPsi') in
          checkSub loc cD cPsi s cPsi' ;
          TClo (tA, s)

    | MVar (Inst ({contents = None}, cPsi', tA, _cnstr), s) -> 
        let _ = dprint (fun () -> "[inferHead] " ^ P.headToString cD cPsi head ) in 
        let _ = dprint (fun () -> "[inferHead] " ^ P.dctxToString cD cPsi ^ "   |-   " ^ 
                          P.subToString cD cPsi s ^ " <= " ^ P.dctxToString cD cPsi') in
          checkSub loc cD cPsi s cPsi' ;
          TClo (tA, s)

    | MMVar (MInst ({contents = None}, cD' , cPsi', tA, _cnstr) , (t', r)) -> 
	let _ = dprint (fun () -> "[inferHead] MMVar " ^ P.headToString cD cPsi head ) in 
	let _ = dprint (fun () -> " cD = " ^ P.mctxToString cD) in 
	let _ = dprint (fun () -> " t' = " ^ P.msubToString cD t' ) in 
	let _ = dprint (fun () -> " cD' = " ^ P.mctxToString cD') in 
	let _ = checkMSub cD (CShift 0, t') cD'  in 
	let _ = dprint (fun () -> "[inferHead] MMVar - msub done \n") in 
	  checkSub loc cD cPsi r (Whnf.cnormDCtx (cPsi', t')) ;
          TClo(Whnf.cnormTyp (tA, t'), r)

  
    | PVar (Offset p, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (_, tA, cPsi') = Whnf.mctxPDec cD p in
          dprnt "[inferHead] PVar case";
          dprint (fun () -> "[inferHead] PVar case:    s = " ^ P.subToString cD cPsi s);
          dprint (fun () -> "check: cPsi' (context of pvar)    = " ^ P.dctxToString cD cPsi' ^ "\n"
                         ^ "check:  cPsi (context in pattern) = " ^ P.dctxToString cD cPsi ^ "\n"
                         ^ "check: synthesizing " ^ P.typToString cD cPsi (tA, s) ^ " for PVar" ^ "\n"
                         ^ "check: cD = " ^ P.mctxToString cD);
          checkSub loc cD cPsi s cPsi';
          (* Check that something of type tA could possibly appear in cPsi *)
          if not (canAppear cD cPsi (tA, s)) then
            raise (Violation ("Parameter variable of type " ^ P.typToString cD cPsi (tA, s)
                            ^ "\ncannot possibly appear in context " ^ P.dctxToString cD cPsi)) ;
          
          (* Return p's type from cD *)
          TClo (tA, s)


  | PVar (PInst ({contents = None}, cPsi', tA, _ ) , s) ->
        (* cD ; cPsi' |- tA <= type *)
          dprnt "[inferHead] PVar case";
          dprint (fun () -> "[inferHead] PVar case:    s = " ^ P.subToString cD cPsi s);
          dprint (fun () -> "check: cPsi' (context of pvar)    = " ^ P.dctxToString cD cPsi' ^ "\n"
                         ^ "check:  cPsi (context in pattern) = " ^ P.dctxToString cD cPsi ^ "\n"
                         ^ "check: synthesizing " ^ P.typToString cD cPsi (tA, s) ^ " for PVar" ^ "\n"
                         ^ "check: cD = " ^ P.mctxToString cD);
          checkSub loc cD cPsi s cPsi';
          (* Check that something of type tA could possibly appear in cPsi *)
          if not (canAppear cD cPsi (tA, s)) then
            raise (Violation ("Parameter variable of type " ^ P.typToString cD cPsi (tA, s)
                            ^ "\ncannot possibly appear in context " ^ P.dctxToString cD cPsi)) ;
          
          (* Return p's type from cD *)
          TClo (tA, s)

    | FVar _ ->
        raise (Error (None, LeftoverFVar))


  and canAppear cD cPsi sA =
    match cPsi with
      | Null -> false

      | CtxVar ctx_var ->
          begin let (Schema elems) = Schema.get_schema (lookupCtxVarSchema cD ctx_var) in
            try let _ = checkTypeAgainstSchema cD (* Null *) cPsi (TClo sA) (* schema *) elems in
                true
            with
              | (Match_failure _) as exn -> raise exn
              | _ -> false
          end

      | DDec (rest, TypDecl(_x, _tB)) ->
          canAppear cD rest sA
        ||
          false (* should check if sA = tB; unimplemented.
                   This should only matter when using a parameter variable 
                     somewhat gratuitously, as p .. x y when the context variable schema
                     doesn't include elements of type sA, but x or y do have type sA *)

  (* checkSub loc cD cPsi s cPsi' = ()
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- s : cPsi'
   *)
  and checkSub loc cD cPsi s cPsi' = match (cPsi, s, cPsi') with
    | (Null, Shift (NoCtxShift, 0), Null) ->
        ()

    | (cPhi, SVar (Offset offset, s'), CtxVar psi')  ->
        begin try
        let (_, cPhi1, cPsi1) = Whnf.mctxSDec cD offset in 
          if cPhi1 = CtxVar psi' then 
            checkSub loc cD cPsi s' cPsi1
          else 
            raise (Error (loc, SubIllTyped ))
        with 
          | _ -> raise (Error (loc, SubIllTyped ))
        end 

    | (CtxVar psi, Shift (NoCtxShift, 0), CtxVar psi')  ->
        (* if psi = psi' then *)
        if subsumes cD psi' psi then
          ()
        else
          raise (Error (loc, CtxVarDiffer (cD, psi, psi')))
            (* (CtxVarMisMatch (psi, psi')) *)

    | (CtxVar (CtxOffset _ as psi), Shift (CtxShift (psi'), 0), Null) ->
        if psi = psi' then
          ()
        else
          raise (Error (None, SubIllTyped))


    | (Null, Shift (NegCtxShift (psi'), 0), CtxVar (CtxOffset _ as psi)) ->
        if psi = psi' then
          ()
        else
          raise (Error (None, SubIllTyped))

    (* SVar case to be added - bp *)

    | (DDec (cPsi, _tX),  Shift (psi, k),  Null) ->
        if k > 0 then
          checkSub loc cD cPsi (Shift (psi, k - 1)) Null
        else
          raise (Error (None, SubIllTyped))

    | (DDec (cPsi, _tX),  Shift (phi, k),  CtxVar psi) ->
        if k > 0 then
          checkSub loc cD cPsi (Shift (phi, k - 1)) (CtxVar psi)
        else
          raise (Violation ("Substitution ill-typed: Shift(_, " ^ string_of_int k ^ ")"))
          (* (SubIllTyped) *)


    | (cPsi',  Shift (psi, k),  cPsi) ->
        if k >= 0 then
          checkSub loc cD cPsi' (Dot (Head (BVar (k + 1)), Shift (psi, k + 1))) cPsi
        else
          raise (Violation ("Substitution ill-formed: Shift(_, " ^ string_of_int k ^ ")"))


(****
This case should now be covered by the one below it

    | (cPsi',  Dot (Head (BVar w), t),  DDec (cPsi, TypDecl(_, Sigma arec))) ->
        (* other heads of type Sigma disallowed -bp *)
        let _ = checkSub cD cPsi' t cPsi
          (* ensures that t is well-typed before comparing types BRec = [t]ARec *)
        and TypDecl (_, Sigma brec) = ctxSigmaDec cPsi' w in
          if not (Whnf.convTypRec (brec, LF.id) (arec, t)) then
            raise (Violation "Sigma-type ill-typed")
            (* (SigmaIllTyped (cD, cPsi', (brec, LF.id), (arec, t))) *)
****)
    (* Add other cases for different heads -bp Fri Jan  9 22:53:45 2009 -bp *)

    | (cPsi',  Dot (Head h, s'),  DDec (cPsi, TypDecl (_, tA2))) ->
        let _   = checkSub loc cD cPsi' s' cPsi
          (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
        and tA1 = inferHead loc cD cPsi' h in
          if Whnf.convTyp (tA1, LF.id) (tA2, s') then
            ()
          else
            let _ = Printf.printf "[checkSub] cPsi' = %s\n           Head h = %s\n           Inferred type: %s\n           Expected type: %s\n\n"
              (P.dctxToString cD cPsi')
              (P.headToString cD cPsi' h)
              (P.typToString cD cPsi' (tA1, LF.id))
              (P.typToString cD cPsi' (tA2, s')) in
              raise (Error (loc, SubIllTyped))
                (* let sM = Root (None, h, Nil) in
                   raise (TypMismatch (cPsi', sM, (tA2, s'), (tA1, LF.id)))  *)

    | (cPsi',  Dot (Obj tM, s'),  DDec (cPsi, TypDecl (_, tA2))) ->
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let _ = checkSub loc cD cPsi' s' cPsi in
          (* ensures that s' is well-typed and [s']tA2 is well-defined *)
          check cD cPsi' (tM, LF.id) (tA2, s')

    | (cPsi1,  s,  cPsi2) ->
        Printf.printf "\n Check substitution: %s  |-  %s  <=  %s\n\n"
          (P.dctxToString cD cPsi1)
          (P.subToString cD cPsi1 s)
          (P.dctxToString cD cPsi2);
        raise (Error (loc, SubIllTyped))


  (*****************)
  (* Kind Checking *)
  (*****************)

  (* kind checking is only applied to type constants declared in
   * the signature;
   *
   * All constants declared in the signature do not contain any
   * contextual variables, hence Delta = .
   *)

  (* synKSpine cD cPsi (tS, s1) (K, s2)
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- [s1]tS <= [s2]K
   *)
  and synKSpine cD cPsi sS1 sK = match (sS1, sK) with
    | ((Nil, _), sK) ->
        sK

    | ((SClo (tS, s'), s), sK) ->
        synKSpine cD cPsi (tS, LF.comp s' s) sK

    | ((App (tM, tS), s1), (PiKind ((TypDecl (_, tA1), _), kK), s2)) ->
        check cD cPsi (tM, s1) (tA1, s2);
        synKSpine cD cPsi (tS, s1) (kK, Dot (Obj (Clo (tM, s1)), s2))

    | ((App _, _), (Typ, _)) ->
        raise SpineMismatch

  (* checkTyp (cD, cPsi, (tA,s))
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- [s]tA <= type
   *)
  and checkTyp' cD cPsi (tA, s) = 

    match tA with
    | Atom (loc, a, tS) ->
        let tK = (Typ.get a).Typ.kind in
        begin try
          let (tK', _s) = synKSpine cD cPsi (tS, s) (tK, LF.id) in
            if tK' = Typ then
              ()
            else
              raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, LF.id)))))
        with SpineMismatch ->
          raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, LF.id)))))
        end

    | PiTyp ((TypDecl (x, tA), _), tB) ->
        checkTyp cD cPsi (tA, s);
        checkTyp cD (DDec (cPsi, TypDecl (x, TClo (tA, s)))) (tB, LF.dot1 s)

    | Sigma arec -> checkTypRec cD cPsi (arec, s)

  and checkTyp cD cPsi sA = checkTyp' cD cPsi (Whnf.whnfTyp sA)


  (* checkTypRec cD cPsi (recA, s)
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- [s]recA <= type
   *)
  and checkTypRec cD cPsi (typRec, s) = match typRec with
    | SigmaLast lastA ->
        checkTyp cD cPsi (lastA, s)

    | SigmaElem(_x, tA, recA) ->
        checkTyp   cD cPsi (tA, s);
        checkTypRec cD
          (DDec (cPsi, LF.decSub (TypDecl (Id.mk_name Id.NoName, tA)) s))
          (recA, LF.dot1 s)


  (* checkKind cD cPsi K
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- K kind
   *)
  and checkKind cD cPsi kind = match kind with
    | Typ ->
        ()

    | PiKind ((TypDecl (x, tA), _), kind) ->
        checkTyp cD cPsi (tA, LF.id);
        checkKind cD (DDec (cPsi, TypDecl (x, tA))) kind


  (* checkDec cD cPsi (x:tA, s)
   *
   * Invariant:
   *
   * succeeds iff ; cD ; cPsi |- [s]tA <= type
   *)
  and checkDec cD cPsi (decl, s) = match decl with
    | TypDecl (_, tA) -> checkTyp cD cPsi (tA, s)


  and synCtxSchema cD (CtxOffset k) =  
    (dprint (fun () -> "[synCtxSchema] lookup k = " ^ R.render_offset k 
	      ^ " in \n cD = " ^ P.mctxToString cD ^ "\n");
     Context.lookupSchema cD k )

  (* checkDCtx cD cPsi
   *
   * Invariant:
   *
   * succeeds iff ; cD |- cPsi ctx
   *)
  and checkDCtx cD cPsi = match cPsi with
    | Null ->  ()
    | DDec (cPsi, tX)     ->
        checkDCtx cD cPsi;
        checkDec cD cPsi (tX, LF.id)

(*    | CtxVar (CtxOffset psi_offset)  ->
        if psi_offset <= (Context.length cO) then
          ()
        else
          raise (Violation "Context variable out of scope")
*)
    | CtxVar psi -> 
        let _ = synCtxSchema cD psi in 
          ()

(* other cases should be impossible -bp *)


  and projectCtxIntoDctx = function
    | Empty -> Null
    | Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

 (* checkTypeAgainstSchema cD cPsi tA sch (elements : sch_elem list)
  *   sch = full schema, for error messages
  *   elements = elements to be tried
  *)
  and checkTypeAgainstSchema cD cPsi tA elements =
    (* if tA is not a Sigma, "promote" it to a one-element typRec *)
    let _ = dprint (fun () ->
                      "checkTypeAgainstSchema "
                    ^ P.typToString cD cPsi (tA, LF.id)
                    ^ "  against  "
                    ^ P.schemaToString (Schema elements)) 
    in
      match elements with
        | [] -> 
            raise (Violation ("Type " ^ P.typToString cD cPsi (tA, LF.id) ^ " doesn't check against schema " ^ P.schemaToString (Schema elements)))
        | element :: elements ->
            try
              instanceOfSchElem cD cPsi (tA, LF.id) element
            with 
              | (Match_failure _) as exn -> raise exn
              | _ -> checkTypeAgainstSchema cD cPsi tA elements

  and instanceOfSchElem cD cPsi (tA, s) (SchElem (some_part, block_part)) = 
    let _ = dprint (fun () -> "instanceOfSchElem...") in 
    let sArec = match Whnf.whnfTyp (tA, s) with
      | (Sigma tArec,s') -> 
          (tArec, s') 
      | (nonsigma, s') -> 
          (SigmaLast nonsigma, s') in
    let _ = dprint (fun () -> "tA =" ^ P.typToString cD cPsi (tA, s)) in 
    let dctx        = projectCtxIntoDctx some_part in
    let _ =  dprint (fun () -> "***Check if it is an instance of a schema element ...") in 
    let _ =  dprint (fun () -> "*** "
                        ^ "\n   cPsi = " ^ P.dctxToString cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cD dctx ) in  

    let _ =  dprint (fun () -> "***Check if it is an instance of a schema element ...") in 
    let dctxSub     = ctxToSub' cPsi dctx in
    let _ = dprint (fun () -> "dctxSub = " ) in 
    let _ = dprint (fun () ->  P.subToString cD cPsi dctxSub) in
    (* let phat        = dctxToHat cPsi in *)
    let _ =  dprint (fun () -> "***Unify.unifyTypRec (" 
                        ^ "\n   cPsi = " ^ P.dctxToString cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cD dctx  
                        ^ "\n   " ^  P.typToString cD cPsi (tA, s) ) in

      (* P.typRecToString cD cPsi sArec  *)
(*    let _ = dprint (fun () -> 
                         "\n== " ^ P.typRecToString cD cPsi (block_part, dctxSub) ) in  *)
    let _ = dprint (fun () ->  "== " ) in 
    let _ = dprint (fun () -> P.typRecToString cD cPsi (block_part, dctxSub) ) in
      begin
        try
          Unify.unifyTypRec cD cPsi sArec (block_part, dctxSub) 
        ; dprint (fun () -> "instanceOfSchElem\n"
                            ^ "  block_part = " ^ P.typRecToString cD cPsi (block_part, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (block_part, dctxSub)
        with (Unify.Unify _) as exn ->
          dprint (fun () -> "Type  "
                    ^ P.typRecToString cD cPsi sArec ^ "  doesn't unify with  "
                    ^ P.typRecToString cD cPsi (block_part, dctxSub));
          raise exn
      end
  
  and instanceOfSchElemProj cD cPsi (tA, s) (var, k) (SchElem (cPhi, trec)) = 
    let tA_k (* : tclo *) = getType var (trec, LF.id) k 1 in
    let _ = dprint (fun () -> "instanceOfSchElemProj...") in
    let (_tA'_k, subst) =
      instanceOfSchElem cD cPsi (tA, s) (SchElem (cPhi, SigmaLast (TClo tA_k)))
      (* tA'_k = [subst] (tA_k) = [s]tA *)
    in
      (trec, subst) 


  (* The rule for checking a context against a schema is
   *
   *  psi::W \in \Omega
   *  -----------------
   *   ... |- psi <= W
   *
   * so checking a context element against a context element is just equality.
   *)
  and checkElementAgainstElement __cD elem1 elem2 =
      let result =
(*         Whnf.convSchElem elem1 elem2 (* (cSome1 = cSome2) && (block1 = block2)  *) in *)
         Whnf.prefixSchElem elem2 elem1 (* (cSome1 = cSome2) && (block1 = block2)  *) in 
        dprint (fun () -> "checkElementAgainstElement "
                         ^ P.schemaToString (Schema[elem1])
                         ^ " <== "
                         ^ P.schemaToString (Schema[elem2])
                         ^ ":  "
                         ^ string_of_bool result);
        result

  (* checkElementAgainstSchema cD sch_elem (elements : sch_elem list) *)
  and checkElementAgainstSchema cD sch_elem elements =
    List.exists (checkElementAgainstElement cD sch_elem) elements

(*  and subset f list = 
    begin match list with [] -> true
      | elem::elems -> f elem 
*)    

  and checkSchema cD cPsi (Schema elements as schema) =
    dprint (fun () -> "checkSchema "  
              ^ P.dctxToString cD cPsi ^ " against " ^ P.schemaToString schema);
    match cPsi with
      | Null -> ()
      | CtxVar (CInst ({contents = Some cPhi}, _, _, _ )) -> 
          checkSchema cD cPhi schema
      | CtxVar ((CtxOffset _ ) as phi) ->
          let Schema phiSchemaElements = 
	    Schema.get_schema (lookupCtxVarSchema cD phi) in
(*            if not (List.forall (fun phiElem -> checkElementAgainstSchema cD phiElem elements) phiSchemaElements) then *)
(*            if not (List.for_all (fun elem -> checkElementAgainstSchema cD elem phiSchemaElements) elements ) then *)
            if List.exists (fun elem -> checkElementAgainstSchema cD elem phiSchemaElements) elements then ()
            else
              raise (Error (None, CtxVarMismatch (cD, phi, schema)))

      | DDec (cPsi', decl) ->
          begin
            checkSchema cD cPsi' schema
          ; match decl with
              | TypDecl (_x, tA) ->
                  let _ = checkTypeAgainstSchema cD cPsi' tA elements in ()
          end


 (* If subsumes psi phi succeeds then there exists  wk_sub  such that  psi |- wk_sub : phi  *)
and subsumes cD psi phi = match (psi, phi) with
  | (CtxOffset psi_var , CtxOffset phi_var) -> 
      let Schema psi_selem = Schema.get_schema (lookupCtxVarSchema cD psi) in 
      let Schema phi_selem = Schema.get_schema (lookupCtxVarSchema cD phi) in 
        List.for_all (fun elem -> checkElementAgainstSchema Empty elem phi_selem) psi_selem  
  | _ -> false


and checkSchemaWf (Schema elements ) = 
    let rec checkElems elements = match elements with
      | [] -> ()
      | SchElem (cPsi, trec) :: els ->
          checkTypRec Empty (projectCtxIntoDctx cPsi) (trec, LF.id) 
          ; checkElems els
    in
      checkElems elements

  (* checkMSub cD ms cD' = () 
  
     if cD |- ms <= cD' then checkMSub succeeds.
 
  *)
and checkMSub cD (cs, ms) cD' = match (ms, cD') with
    | (MShift k, Empty) ->  
        if (Context.length cD) = k then () 
        else 
          raise (Violation ("Contextual substitution ill-typed - 1"))

    | (MShift k, cD') -> 
	if k >= 0 then 
	  checkMSub cD (cs, MDot (MV (k+1), MShift (k+1))) cD'
	else raise (Violation ("Contextual substitution ill-formed"))

    | (MDot (MObj(_ , tM), ms), Dec(cD1', MDecl (_u, tA, cPsi))) -> 
        let cPsi' = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx  (cPsi, ms), cs) in 
        let tA'   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tA, ms), cs) in
        (check cD cPsi' (tM, LF.id) (tA', LF.id) ; 
         checkMSub cD (cs, ms) cD1')

    | (MDot (CObj(cPsi), ms), Dec(cD1', CDecl (_psi, w, _))) -> 
        (checkSchema cD cPsi (Schema.get_schema w) ; 
         checkMSub cD (cs, ms) cD1')

    | (MDot (MV u, ms), Dec(cD1', MDecl (_u, tA, cPsi))) -> 
        let cPsi' = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx  (cPsi, ms), cs) in 
        let tA'   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tA, ms), cs) in
        let (_, tA1, cPsi1) = Whnf.mctxMDec cD u in 
          if Whnf.convDCtx cPsi1 cPsi' && Whnf.convTyp (tA', LF.id) (tA1, LF.id) then 
                     checkMSub cD (cs, ms) cD1'
          else 
            raise (Violation ("Contextual substitution ill-typed - 2 "))

    | (MDot (MV p, ms), Dec(cD1', PDecl (_u, tA, cPsi))) -> 
        let cPsi' = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx  (cPsi, ms), cs) in 
        let tA'   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tA, ms), cs) in
        let (_, tA1, cPsi1) = Whnf.mctxPDec cD p in 
          if Whnf.convDCtx cPsi1 cPsi' && Whnf.convTyp (tA', LF.id) (tA1, LF.id) then 
            checkMSub cD (cs, ms) cD1'
          else 
            raise (Violation ("Contextual substitution ill-typed - 3 "))

    | (MDot (PObj (_, h), ms), Dec(cD1', PDecl (_u, tA, cPsi))) -> 
        let cPsi' = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx  (cPsi, ms), cs) in 
        let tA'   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tA, ms), cs) in
          (begin match h with
            | BVar k -> 
                let TypDecl (_, tB) = ctxDec cPsi' k in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
            | PVar _ -> 
                let tB = inferHead None cD cPsi' h in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
            | Proj _ -> 
                let tB = inferHead None cD cPsi' h in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
           end ;
           checkMSub cD (cs, ms) cD1')

    | (_, _ ) -> 
        raise (Violation ("Contextual substitution ill-typed\n " ^ 
                            P.mctxToString cD ^ " |- " ^ 
                            P.msubToString cD ms ^ " <= "  
                         ^ " = " ^ P.mctxToString cD'))
