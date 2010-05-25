(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [5])


module LF = struct
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
    | Null -> LF.id
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
        let u     = Whnf.etaExpandMV cPhi (tA, LF.comp s (ctxShift cPhi)) LF.id in 
        let front = (Obj ((* Root(MVar(u, S.LF.id), Nil) *) u) : front) in
          Dot (front, LF.comp s LF.shift)


  (* check cO cD cPsi (tM, s1) (tA, s2) = ()
   *
   * Invariant:
   *
   * If   cO ; cD ; cPsi |- s1 <= cPsi1
   * and  cO ; cD ; cPsi |- s2 <= cPsi2    cPsi2 |- tA <= type
   * returns ()
   * if there exists an tA' s.t.
   * cO ; cD ; cPsi1 |- tM      <= tA'
   * and  cO ; cD ; cPsi  |- tA'[s1]  = tA [s2] : type
   * and  cO ; cD ; cPsi  |- tM [s1] <= tA'[s1]
   * otherwise exception Error is raised
   *)
  let rec checkW cO cD cPsi sM sA = match (sM, sA) with
    | ((Lam (_, _, tM), s1),   (PiTyp ((TypDecl (_x, _tA) as tX, _), tB), s2)) -> 
        check cO cD
          (DDec (cPsi, LF.decSub tX s2))
          (tM, LF.dot1 s1)
          (tB, LF.dot1 s2)

    | ((Tuple (_, tuple), s1),   (Sigma typRec, s2)) -> 
        checkTuple cO cD cPsi (tuple, s1) (typRec, s2)

    | ((Root (loc, _h, _tS), _s (* id *)),   (Atom _, _s')) ->
        (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
          begin try
            let _ = dprint (fun () -> "[check] " ^ P.normalToString cO cD cPsi sM ^ 
                              " <= " ^ P.typToString cO cD cPsi sA ) in
            let sP = syn' cO cD cPsi sM in 
            let _ = dprint (fun () -> "[check] synthesized " ^ P.normalToString cO cD cPsi sM ^ 
                              " => " ^ P.typToString cO cD cPsi sP ) in
            let (tP', tQ') = (Whnf.normTyp sP , Whnf.normTyp sA) in 
              if not (Whnf.convTyp  (tP', LF.id) (tQ', LF.id)) then 
                (dprint (fun () -> "here!") ; 
                raise (Error (loc, TypMismatch (cO, cD, cPsi, sM, sA, sP))))
          with SpineMismatch ->
            raise (Error (loc, (IllTyped (cO, cD, cPsi, sM, sA))))
          end

    | ((Lam (loc, _, _), _), _) ->
       raise (Error (loc, IllTyped (cO, cD, cPsi, sM, sA)))

    | ((Root (loc, _, _), _), _) ->
       raise (Error (loc, IllTyped (cO, cD, cPsi, sM, sA)))

  and check cO cD cPsi sM sA = checkW cO cD cPsi (Whnf.whnf sM) (Whnf.whnfTyp sA)

  and checkTuple cO cD cPsi (tuple, s1) (typRec, s2) = match (tuple, typRec) with
    | (Last tM,   SigmaLast tA) ->
        checkW cO cD cPsi (tM, s1) (tA, s2)

    | (Cons (tM, restOfTuple),   SigmaElem (_x, tA, restOfTypRec)) ->
        checkW cO cD cPsi (tM, s1) (tA, s2)
      ; checkTuple cO cD cPsi
          (restOfTuple, s1)
          (restOfTypRec, Dot (Obj tM, s2))

    | (_, _) ->
        raise (Violation ("checkTuple arity mismatch"))


  and syn' cO cD cPsi (Root (loc, h, tS), s (* id *)) = 
    let sA' = Whnf.whnfTyp (inferHead loc cO cD cPsi h, LF.id) in
      synSpine cO cD cPsi (tS, s) sA'       
        

  and syn cO cD cPsi ((Root (loc, _h, _tS), _s (* id *)) as sR) = 
    begin try
      syn' cO cD cPsi sR
    with SpineMismatch -> 
      raise (Error (loc, SpineIllTyped))
    end

  (* synSpine cO cD cPsi sS sA = sP
   * 
   * Invariant:
   *
   * cO ; cD ; cPsi sS : sA => sP
   *)
  and synSpine cO cD cPsi sS sA = match (sS, sA) with
    | ((Nil, _),   sP) ->
        sP
    
    | ((SClo (tS, s'), s),   sA) ->
        synSpine cO cD cPsi (tS, LF.comp s' s) sA
    
    | ((App (tM, tS), s1),   (PiTyp ((TypDecl (_, tA1), _), tB2), s2)) ->
        check cO cD cPsi (tM, s1) (tA1, s2);
        (*     cD ; cPsi1        |- tM  <= tA1'
         * and cD ; cPsi         |- s1  <= cPsi1
         * and cD ; cPsi2, x:tA1 |- tB2 <= type
         * and [s1]tA1' = [s2]tA1
         *)
        let tB2 = Whnf.whnfTyp (tB2, Dot (Obj (Clo (tM, s1)), s2)) in
          synSpine cO cD cPsi (tS, s1) tB2
    
    | ((App _, _),   (Atom _, _)) ->
        raise SpineMismatch

(* TODO: move this function somewhere else, and get rid of duplicate in reconstruct.ml  -jd 2009-03-14 *)

  (* inferHead loc cO cD cPsi h = tA
   *
   * Invariant:
   *
   * returns tA if
   * cO cD ; cPsi |- h => tA
   * where cO cD ; cPsi |- tA <= type
   * else exception Error is raised.
   *)
  and inferHead loc cO cD cPsi head = match head with
    | BVar k' ->
        let (_, _l) = dctxToHat cPsi in
        let TypDecl (_, tA) = ctxDec cPsi k' in
          tA
    
    | Proj (tuple_head, target) ->
        let srecA = match tuple_head with
          | BVar k' ->
              let TypDecl (_, Sigma recA) = ctxSigmaDec cPsi k' in
              let _ = dprint (fun () -> "[InferHead] " ^ P.dctxToString cO cD cPsi) in
              let _ = dprint (fun () -> "|-  " ^  P.headToString cO cD cPsi head ^ "\n" ^ 
                                " where " ^ P.headToString cO cD cPsi tuple_head ^ " has type " ^ P.typRecToString cO cD cPsi (recA, LF.id) ^ "\n") in
                (recA, LF.id)
          | PVar (Offset p, s) ->
              begin let (_, tTuple, cPsi') = Whnf.mctxPDec cD p in

                checkSub loc cO cD cPsi s cPsi';
                match tTuple with
                    Sigma recA -> (recA, s)
              end
        in
        let (_tA, s) as sA = getType tuple_head srecA target 1 in 
        let _ = dprint (fun () -> "getTyp ( " ^ P.headToString cO cD cPsi head ^ " ) = " ^ P.typToString cO cD cPsi sA ^ "\n") in 
        let _ = dprint (fun () -> "s = " ^ P.subToString cO cD cPsi s ^ "\n") in
          TClo sA

    
    | Const c ->
        (Term.get c).Term.typ
    
    | MVar (Offset u, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (_, tA, cPsi') = Whnf.mctxMDec cD u in
        let _ = dprint (fun () -> "[inferHead] " ^ P.headToString cO cD cPsi head ) in 
        let _ = dprint (fun () -> "[inferHead] " ^ P.dctxToString cO cD cPsi ^ "   |-   " ^ 
                          P.subToString cO cD cPsi s ^ " <= " ^ P.dctxToString cO cD cPsi') in
          checkSub loc cO cD cPsi s cPsi' ;
          TClo (tA, s)
    
    | PVar (Offset p, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (_, tA, cPsi') = Whnf.mctxPDec cD p in
          checkSub loc cO cD cPsi s cPsi' ;
          dprint (fun () -> "check: cPsi' (context of pvar)    = " ^ P.dctxToString cO cD cPsi') ;
          dprint (fun () -> "check:  cPsi (context in pattern) = " ^ P.dctxToString cO cD cPsi) ;
          dprint (fun () -> "check: synthesizing " ^ P.typToString cO cD cPsi (tA, s) ^ " for PVar") ;
          dprint (fun () -> "check: [Show OCtx] cO = " ^ P.octxToString cO ) ; 
          dprint (fun () -> "check: [Show MCtx] cD = " ^ P.mctxToString cO cD) ;  
          (* Check that something of type tA could possibly appear in cPsi *)
          if not (canAppear cO cD cPsi (tA, s)) then
            raise (Violation ("Parameter variable of type " ^ P.typToString cO cD cPsi (tA, s)
                            ^ "\ncannot possibly appear in context " ^ P.dctxToString cO cD cPsi)) ;
          
          (* Return p's type from cD *)
          TClo (tA, s)

    | FVar _ ->
        raise (Error (None, LeftoverFVar))


  and canAppear cO cD cPsi sA =
    match cPsi with
      | Null -> false

      | CtxVar ctx_var ->
          begin let (Schema elems) = Schema.get_schema (lookupCtxVarSchema cO ctx_var) in
            try let _ = checkTypeAgainstSchema cO cD Null (TClo sA) (* schema *) elems in
                true
            with
              | (Match_failure _) as exn -> raise exn
              | _ -> false
          end

      | DDec (rest, TypDecl(_x, _tB)) ->
          canAppear cO cD rest sA
        ||
          false (* should check if sA = tB; unimplemented.
                   This should only matter when using a parameter variable 
                     somewhat gratuitously, as p .. x y when the context variable schema
                     doesn't include elements of type sA, but x or y do have type sA *)

  (* checkSub loc cO cD cPsi s cPsi' = ()
   *
   * Invariant:
   *
   * succeeds iff cO cD ; cPsi |- s : cPsi'
   *)
  and checkSub loc cO cD cPsi s cPsi' = match (cPsi, s, cPsi') with
    | (Null, Shift (NoCtxShift, 0), Null) ->
        ()

    | (cPhi, SVar (Offset offset, s'), CtxVar psi')  ->
        begin try
        let (_, cPhi1, cPsi1) = Whnf.mctxSDec cD offset in 
          if cPhi1 = CtxVar psi' then 
            checkSub loc cO cD cPsi s' cPsi1
          else 
            raise (Error (loc, SubIllTyped ))
        with 
          | _ -> raise (Error (loc, SubIllTyped ))
        end 

    | (CtxVar psi, Shift (NoCtxShift, 0), CtxVar psi')  ->
        (* if psi = psi' then *)
        if subsumes cO psi' psi then
          ()
        else
          raise (Error (loc, CtxVarDiffer (cO, psi, psi')))
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
          checkSub loc cO cD cPsi (Shift (psi, k - 1)) Null
        else
          raise (Error (None, SubIllTyped))

    | (DDec (cPsi, _tX),  Shift (phi, k),  CtxVar psi) ->
        if k > 0 then
          checkSub loc cO cD cPsi (Shift (phi, k - 1)) (CtxVar psi)
        else
          raise (Violation ("Substitution ill-typed: k = %s" ^ (string_of_int k)))
          (* (SubIllTyped) *)


    | (cPsi',  Shift (psi, k),  cPsi) ->
        checkSub loc cO cD cPsi' (Dot (Head (BVar (k + 1)), Shift (psi, k + 1))) cPsi


(****
This case should now be covered by the one below it

    | (cPsi',  Dot (Head (BVar w), t),  DDec (cPsi, TypDecl(_, Sigma arec))) ->
        (* other heads of type Sigma disallowed -bp *)
        let _ = checkSub cO cD cPsi' t cPsi
          (* ensures that t is well-typed before comparing types BRec = [t]ARec *)
        and TypDecl (_, Sigma brec) = ctxSigmaDec cPsi' w in
          if not (Whnf.convTypRec (brec, LF.id) (arec, t)) then
            raise (Violation "Sigma-type ill-typed")
            (* (SigmaIllTyped (cD, cPsi', (brec, LF.id), (arec, t))) *)
****)
    (* Add other cases for different heads -bp Fri Jan  9 22:53:45 2009 -bp *)

    | (cPsi',  Dot (Head h, s'),  DDec (cPsi, TypDecl (_, tA2))) ->
        let _   = checkSub loc cO cD cPsi' s' cPsi
          (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
        and tA1 = inferHead loc cO cD cPsi' h in
          if Whnf.convTyp (tA1, LF.id) (tA2, s') then
            ()
          else
            let _ = Printf.printf "[checkSub] cPsi' = %s \n Head h = %s \n Inferred type: %s\n Expected type: %s\n\n"
              (P.dctxToString cO cD cPsi')
              (P.headToString cO cD cPsi' h)
              (P.typToString cO cD cPsi' (tA1, LF.id))
              (P.typToString cO cD cPsi' (tA2, s')) in
              raise (Error (loc, SubIllTyped))
                (* let sM = Root (None, h, Nil) in
                   raise (TypMismatch (cPsi', sM, (tA2, s'), (tA1, LF.id)))
                *)

    | (cPsi',  Dot (Obj tM, s'),  DDec (cPsi, TypDecl (_, tA2))) ->
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let _ = checkSub loc cO cD cPsi' s' cPsi in
          (* ensures that s' is well-typed and [s']tA2 is well-defined *)
          check cO cD cPsi' (tM, LF.id) (tA2, s')

    | (cPsi1,  s,  cPsi2) ->
        Printf.printf "\n Check substitution: %s   |-    %s    <= %s  \n\n"
          (P.dctxToString cO cD cPsi1)
          (P.subToString cO cD cPsi1 s)
          (P.dctxToString cO cD cPsi2);
        raise (Error (loc, SubIllTyped))

(* (Violation "Substitution is ill-typed; this case should be impossible.\n")*)

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
  and synKSpine cO cD cPsi sS1 sK = match (sS1, sK) with
    | ((Nil, _), sK) ->
        sK

    | ((SClo (tS, s'), s), sK) ->
        synKSpine cO cD cPsi (tS, LF.comp s' s) sK

    | ((App (tM, tS), s1), (PiKind ((TypDecl (_, tA1), _), kK), s2)) ->
        check cO cD cPsi (tM, s1) (tA1, s2);
        synKSpine cO cD cPsi (tS, s1) (kK, Dot (Obj (Clo (tM, s1)), s2))

    | ((App _, _), (Typ, _)) ->
        raise SpineMismatch

  (* checkTyp (cD, cPsi, (tA,s))
   *
   * Invariant:
   *
   * succeeds iff cD ; cPsi |- [s]tA <= type
   *)
  and checkTyp' cO cD cPsi (tA, s) = 

    match tA with
    | Atom (loc, a, tS) ->
        let tK = (Typ.get a).Typ.kind in
        begin try
          let (tK', _s) = synKSpine cO cD cPsi (tS, s) (tK, LF.id) in
            if tK' = Typ then
              ()
            else
              raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, LF.id)))))
        with SpineMismatch ->
          raise (Error (loc, (KindMismatch (cD, cPsi, (tS, s), (tK, LF.id)))))
        end

    | PiTyp ((TypDecl (x, tA), _), tB) ->
        checkTyp cO cD cPsi (tA, s);
        checkTyp cO cD (DDec (cPsi, TypDecl (x, TClo (tA, s)))) (tB, LF.dot1 s)

    | Sigma arec -> checkTypRec cO cD cPsi (arec, s)

  and checkTyp cO cD cPsi sA = checkTyp' cO cD cPsi (Whnf.whnfTyp sA)


  (* checkTypRec cO cD cPsi (recA, s)
   *
   * Invariant:
   *
   * succeeds iff cO cD ; cPsi |- [s]recA <= type
   *)
  and checkTypRec cO cD cPsi (typRec, s) = match typRec with
    | SigmaLast lastA ->
        checkTyp cO cD cPsi (lastA, s)

    | SigmaElem(_x, tA, recA) ->
        checkTyp  cO  cD cPsi (tA, s);
        checkTypRec cO cD
          (DDec (cPsi, LF.decSub (TypDecl (Id.mk_name Id.NoName, tA)) s))
          (recA, LF.dot1 s)


  (* checkKind cO cD cPsi K
   *
   * Invariant:
   *
   * succeeds iff cO cD ; cPsi |- K kind
   *)
  and checkKind cO cD cPsi kind = match kind with
    | Typ ->
        ()

    | PiKind ((TypDecl (x, tA), _), kind) ->
        checkTyp cO cD cPsi (tA, LF.id);
        checkKind cO cD (DDec (cPsi, TypDecl (x, tA))) kind


  (* checkDec cO cD cPsi (x:tA, s)
   *
   * Invariant:
   *
   * succeeds iff cO ; cD ; cPsi |- [s]tA <= type
   *)
  and checkDec cO cD cPsi (decl, s) = match decl with
    | TypDecl (_, tA) -> checkTyp cO cD cPsi (tA, s)


  and synCtxSchema cO (CtxOffset k) =  Context.lookupSchema cO k 

  (* checkDCtx cO cD cPsi
   *
   * Invariant:
   *
   * succeeds iff cO ; cD |- cPsi ctx
   *)
  and checkDCtx cO  cD cPsi = match cPsi with
    | Null ->  ()
    | DDec (cPsi, tX)     ->
        checkDCtx cO cD cPsi;
        checkDec cO cD cPsi (tX, LF.id)

(*    | CtxVar (CtxOffset psi_offset)  ->
        if psi_offset <= (Context.length cO) then
          ()
        else
          raise (Violation "Context variable out of scope")
*)
    | CtxVar psi -> 
        let _ = synCtxSchema cO psi in 
          ()

(* other cases should be impossible -bp *)


  and projectCtxIntoDctx = function
    | Empty -> Null
    | Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

 (* checkTypeAgainstSchema cO cD cPsi tA sch (elements : sch_elem list)
  *   sch = full schema, for error messages
  *   elements = elements to be tried
  *)
  and checkTypeAgainstSchema cO cD cPsi tA elements =
    (* if tA is not a Sigma, "promote" it to a one-element typRec *)
    let _ = dprint (fun () ->
                      "checkTypeAgainstSchema "
                    ^ P.typToString cO cD cPsi (tA, LF.id)
                    ^ "  against  "
                    ^ P.schemaToString (Schema elements)) 
    in
      match elements with
        | [] -> 
            raise (Violation ("Type " ^ P.typToString cO cD cPsi (tA, LF.id) ^ " doesn't check against schema " ^ P.schemaToString (Schema elements)))
        | element :: elements ->
            try
              instanceOfSchElem cO cD cPsi (tA, LF.id) element
            with 
              | (Match_failure _) as exn -> raise exn
              | _ -> checkTypeAgainstSchema cO cD cPsi tA elements

  and instanceOfSchElem cO cD cPsi (tA, s) (SchElem (some_part, block_part)) = 
    let _ = dprint (fun () -> "instanceOfSchElem...") in 
    let sArec = match Whnf.whnfTyp (tA, s) with
      | (Sigma tArec,s') -> 
          (tArec, s') 
      | (nonsigma, s') -> 
          (SigmaLast nonsigma, s') in
    let _ = dprint (fun () -> "tA =" ^ P.typToString cO cD cPsi (tA, s)) in 
    let dctx        = projectCtxIntoDctx some_part in
    
    let dctxSub     = ctxToSub' cPsi dctx in

    (* let phat        = dctxToHat cPsi in *)

    let _ =  dprint (fun () -> "***Unify.unifyTypRec (" 
                        ^ "\n   cPsi = " ^ P.dctxToString cO cD cPsi
                        ^ "\n   dctx = " ^ P.dctxToString cO cD dctx  
                        ^ "\n   " ^  P.typToString cO cD cPsi (tA, s) ) in
    let _ = dprint (fun () -> "dctxSub = " ^ P.subToString cO cD cPsi dctxSub ^ "\n") in
      (* P.typRecToString cO cD cPsi sArec  *)
(*    let _ = dprint (fun () -> 
                         "\n== " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) ) in  *)
    let _ = dprint (fun () ->  "== " ) in 
    let _ = dprint (fun () -> P.typRecToString cO cD cPsi (block_part, dctxSub) ) in
      begin
        try
          Unify.unifyTypRec cD cPsi sArec (block_part, dctxSub) 
        ; dprint (fun () -> "instanceOfSchElem\n"
                            ^ "  block_part = " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (block_part, dctxSub)
        with (Unify.Unify _) as exn ->
          dprint (fun () -> "Type  "
                    ^ P.typRecToString cO cD cPsi sArec ^ "  doesn't unify with  "
                    ^ P.typRecToString cO cD cPsi (block_part, dctxSub));
          raise exn
      end
  
  and instanceOfSchElemProj cO cD cPsi (tA, s) (var, k) (SchElem (cPhi, trec)) = 
    let tA_k (* : tclo *) = getType var (trec, LF.id) k 1 in
    let _ = dprint (fun () -> "instanceOfSchElemProj...") in
    let (_tA'_k, subst) =
      instanceOfSchElem cO cD cPsi (tA, s) (SchElem (cPhi, SigmaLast (TClo tA_k)))
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
  and checkElementAgainstElement _cO _cD elem1 elem2 =
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

  (* checkElementAgainstSchema cO cD sch_elem (elements : sch_elem list) *)
  and checkElementAgainstSchema cO cD sch_elem elements =
    List.exists (checkElementAgainstElement cO cD sch_elem) elements

(*  and subset f list = 
    begin match list with [] -> true
      | elem::elems -> f elem 
*)    

  and checkSchema cO cD cPsi (Schema elements as schema) =
    dprint (fun () -> "checkSchema " ^ P.octxToString cO ^ " ... " 
              ^ P.dctxToString cO cD cPsi ^ " against " ^ P.schemaToString schema);
    match cPsi with
      | Null -> ()
      | CtxVar (CInst ({contents = Some cPhi}, _, _, _ )) -> 
          checkSchema cO cD cPhi schema
      | CtxVar ((CtxOffset _ ) as phi) ->
          let Schema phiSchemaElements = Schema.get_schema (lookupCtxVarSchema cO phi) in
(*            if not (List.forall (fun phiElem -> checkElementAgainstSchema cO cD phiElem elements) phiSchemaElements) then *)
(*            if not (List.for_all (fun elem -> checkElementAgainstSchema cO cD elem phiSchemaElements) elements ) then *)
            if (List.exists (fun elem -> checkElementAgainstSchema cO cD elem phiSchemaElements) elements ) then ()
              else
                raise (Error (None, CtxVarMismatch (cO, phi, schema)))

      | DDec (cPsi', decl) ->
          begin
            checkSchema cO cD cPsi' schema
          ; match decl with
              | TypDecl (_x, tA) ->
                  let _ = checkTypeAgainstSchema cO cD cPsi' tA elements in ()
          end


 (* If subsumes cO psi phi succeeds then there exists a wk_sub s.t. psi |- wk_sub   : phi  *)
and subsumes cO psi phi = match (psi, phi) with
  | (CtxOffset psi_var , CtxOffset phi_var) -> 
      let Schema psi_selem = Schema.get_schema (lookupCtxVarSchema cO psi) in 
      let Schema phi_selem = Schema.get_schema (lookupCtxVarSchema cO phi) in 
        List.for_all (fun elem -> checkElementAgainstSchema cO Empty elem phi_selem) psi_selem  
  | _ -> false


  let rec checkSchemaWf (Schema elements ) = 
    let rec checkElems elements = match elements with
      | [] -> ()
      | SchElem (cPsi, trec) :: els ->
          checkTypRec Empty Empty (projectCtxIntoDctx cPsi) (trec, LF.id) 
          ; checkElems els
    in
      checkElems elements

  (* checkMSub cD ms cD' = () 
  
     if cD |- ms <= cD' then checkMSub succeeds.
 
  *)
  let rec checkMSub cO cD ms cD' = match (ms, cD') with
    | (MShift k, Empty) ->  
        if (Context.length cD) = k then () 
        else 
          raise (Violation ("Contextual substitution ill-typed - 1"))
    | (MDot (MObj(_ , tM), ms), Dec(cD1', MDecl (_u, tA, cPsi))) -> 
        let cPsi' = Whnf.cnormDCtx  (cPsi, ms) in 
        let tA'   = Whnf.cnormTyp (tA, ms) in
        (check cO cD cPsi' (tM, LF.id) (tA', LF.id) ; 
         checkMSub cO cD ms cD1')

    | (MDot (MV u, ms), Dec(cD1', MDecl (_u, tA, cPsi))) -> 
        let cPsi' = Whnf.cnormDCtx  (cPsi, ms) in 
        let tA'   = Whnf.cnormTyp (tA, ms) in
        let (_, tA1, cPsi1) = Whnf.mctxMDec cD u in 
          if Whnf.convDCtx cPsi1 cPsi' && Whnf.convTyp (tA', LF.id) (tA1, LF.id) then 
                     checkMSub cO cD ms cD1'
          else 
            raise (Violation ("Contextual substitution ill-typed - 2 "))

    | (MDot (MV p, ms), Dec(cD1', PDecl (_u, tA, cPsi))) -> 
        let cPsi' = Whnf.cnormDCtx  (cPsi, ms) in 
        let tA'   = Whnf.cnormTyp (tA, ms) in
        let (_, tA1, cPsi1) = Whnf.mctxPDec cD p in 
          if Whnf.convDCtx cPsi1 cPsi' && Whnf.convTyp (tA', LF.id) (tA1, LF.id) then 
            checkMSub cO cD ms cD1'
          else 
            raise (Violation ("Contextual substitution ill-typed - 3 "))

    | (MDot (PObj (_, h), ms), Dec(cD1', PDecl (_u, tA, cPsi))) -> 
        let cPsi' = Whnf.cnormDCtx  (cPsi, ms) in 
        let tA'   = Whnf.cnormTyp (tA, ms) in
          (begin match h with
            | BVar k -> 
                let TypDecl (_, tB) = ctxDec cPsi' k in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
            | PVar _ -> 
                let tB = inferHead None cO cD cPsi' h in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
            | Proj _ -> 
                let tB = inferHead None cO cD cPsi' h in 
                  if Whnf.convTyp (tB, LF.id) (tA', LF.id) then ()
          end ;
          checkMSub cO cD ms cD1')
    | (_, _ ) -> 
        raise (Violation ("Contextual substitution ill-typed ?\n " ^ 
                            P.mctxToString cO cD ^ " |- " ^ 
                            P.msubToString cO cD ms ^ " <= "  
                         ^ " = " ^ P.mctxToString cO cD' ^ "\n"))



end (* struct LF*)

module Comp = struct

  module E = Error

  module Unify = Unify.EmptyTrail
    (* NOTES on handling context variables: -bp
     *
     *  - We should maybe put context variables into a context Omega (not Delta)
     *    It makes it difficult to deal with branches.
     *
     *  Recall: Case(e, branches)  where branch 1 = Pi Delta1. box(psihat. tM1) : A1[Psi1] -> e1
     *
     *  Note that any context variable occurring in Delta, psihat, A and Psi is bound OUTSIDE.
     *  So if
     *
     *  D ; G |- Case (e, branches)  and ctxvar psi in D the branch 1 is actually well formed iff
     *
     *  D, D1 ; Psi1 |- tM1 <= tA1  (where only psi declared in D is relevant to the rest.)
     *
     *  Also, ctx variables are not subject to instantiations during unification / matching
     *  which is used in type checking and type reconstruction.
     *
     *  This has wider implications;
     *
     * - revise indexing structure; the offset of ctxvar is with respect to
     *   a context Omega
     *
     * - Applying substitution for context variables; does it make sense to
     *   deal with it lazily? – It seems complicated to handle lazy context substitutions
     *   AND lazy msubs.
     *
     *  If we keep them in Delta, we need to rewrite mctxToMSub for example;
     *)

  open Context
  open Store.Cid
  open Syntax.Int.Comp

  module S = Substitution
  module I = Syntax.Int.LF
  module C = Whnf

  module P = Pretty.Int.DefaultPrinter

  type caseType =
    | IndexObj of I.psi_hat * I.normal
    | DataObj 

  exception Violation of string
  exception Error of Syntax.Loc.t option * E.error

  let rec length cD = match cD with
    | I.Empty -> 0
    | I.Dec(cD, _) -> 1 + length cD

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (_,  tau)), 1) -> tau
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let rec split tc d = match (tc, d) with
    | (tc, 0) -> tc
    | (I.MDot (_ft, t), d) -> split t (d - 1)

(*** moved to Ctxsub
  let rec mctxToMSub cD = match cD with
    | I.Empty -> 
        C.m_id

    | I.Dec (cD', I.MDecl(_, tA, cPsi)) ->
        let t     = mctxToMSub cD' in
        let cPsi' = Whnf.cnormDCtx (cPsi, t) in
        let tA'   = Whnf.cnormTyp (tA, t) in
        let u     = Whnf.newMVar (cPsi', tA') in
        let phat  = Context.dctxToHat cPsi (*** cPsi' or cPsi? ***) in
          I.MDot (I.MObj (phat, I.Root (None, I.MVar (u, S.LF.id), I.Nil)), t)

    | I.Dec (cD', I.PDecl(_, tA, cPsi)) ->
        let t    = mctxToMSub cD' in
        let p    = Whnf.newPVar (Whnf.cnormDCtx (cPsi, t),  Whnf.cnormTyp (tA, t)) in
        let phat = Context.dctxToHat cPsi in  (*** cPsi' or cPsi? ***)
          I.MDot (I.PObj (phat, I.PVar (p, S.LF.id)), t)
***)
  let mctxToMSub = Ctxsub.mctxToMSub

  (* extend t1 t2 = t
   *
   * Invariant:
   * If    . |- t1 <= cD1
   *   and . |- t2 <= cD2
   *   and FMV(cD1) intersect FMV(cD2) = {}
   *   (i.e. no modal variable occurring in type declarations in cD1
   *    also occurs in a type declaration of cD2)
   * then
   *       . |- t1,t2 <= cD1, cD2   and t = t1,t2
   *)
  let extend t1 t2 = 
    let rec ext t2 = match t2 with
      | I.MShift 0     -> t1
      | I.MDot (ft, t) -> I.MDot (ft, ext t)
      (* other cases should be impossible *)
    in ext t2;;


  let rec checkTyp cO cD tau =

    match tau with
        
    | TypBox (_ , tA, cPsi) ->
        LF.checkDCtx cO cD cPsi;
        LF.checkTyp  cO cD cPsi (tA, S.LF.id)

    | TypSub (_ , cPhi, cPsi) ->
        LF.checkDCtx cO cD cPsi;
        LF.checkDCtx cO cD cPhi
          
    | TypArr (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2
          
    | TypCross (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2
          
    | TypCtxPi ((psi_name, schema_cid, _ ), tau) ->
        checkTyp (I.Dec (cO, I.CDecl (psi_name, schema_cid))) cD tau
          
    | TypPiBox ((cdecl, _), tau) ->
        checkTyp cO (I.Dec (cD, cdecl)) tau 

    | TypBool -> ()

;;


  (* check cO cD cG e (tau, theta) = ()
   *
   * Invariant:
   *
   * If  cO ; cD ; cG |- e wf-exp
   * and cO ; cD |- theta <= cD'
   * and cO ; cD'|- tau <= c_typ
   * returns ()
   * if  cO ; cD ; cG |- e <= [|t|]tau
   *
   * otherwise exception Error is raised
   *)
  
  let rec checkW cO cD (cG : ctyp_decl I.ctx) e ttau = match (e, ttau) with
    | (Rec (_, f, e), (tau, t)) ->
        check cO cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))) e ttau

    | (Fun (_, x, e), (TypArr (tau1, tau2), t)) ->
        check cO cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t)))) e (tau2, t)

    | (CtxFun (_, psi, e), (TypCtxPi ((_psi, schema, _ ), tau), t)) ->
        check (I.Dec(cO, I.CDecl(psi, schema))) cD cG e (tau, t)

    | (MLam (_, u, e), (TypPiBox ((I.MDecl(_u, tA, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.MDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.PDecl(_u, tA, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.PDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (MLam (_, u, e), (TypPiBox ((I.SDecl(_u, cPhi, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.SDecl(u, C.cnormDCtx (cPhi, t), C.cnormDCtx (cPsi, t))))
          (C.cnormCtx (cG, I.MShift 1))   e (tau, C.mvar_dot1 t)

    | (Pair (_, e1, e2), (TypCross (tau1, tau2), t)) ->
        check cO cD cG e1 (tau1, t);
        check cO cD cG e2 (tau2, t)

    | (LetPair (_, i, (x, y, e)), (tau, t)) ->
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cO cD cG' e (tau,t)
          | _ -> raise (Violation "Case scrutinee not of boxed type")
        end

    | (Box (_, _phat, tM), (TypBox (_, tA, cPsi), t)) ->
        begin try
(*        Already done during cwhnfCTyp ... -bp
          let cPsi' = C.cnormDCtx (cPsi, t) in
          let tA'   = C.cnormTyp (tA, t) in
*)
            LF.check cO cD  cPsi (tM, S.LF.id) (tA, S.LF.id)
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Violation ("Free meta-variable " ^ (R.render_name u)))
        end

    | (SBox (loc , _phat, sigma), (TypSub (_, cPhi, cPsi), t)) ->
        begin try
            LF.checkSub loc cO cD  cPsi sigma cPhi
        with Whnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Violation ("Free meta-variable " ^ (R.render_name u)))
        end

(*    | (SBox (loc , phat, sigma), tau_t) ->
        raise (Violation  ("Found SBox " ^ P.subToString cO cD (Context.hatToDCtx phat) sigma ^ 
                             "\n supposed to have type " ^ P.compTypToString cO cD (Whnf.cnormCTyp tau_t) ^ "\n"))


    | (Box (loc , phat, tM), tau_t) ->
        raise (Violation  ("Found Box " ^ P.normalToString cO cD (Context.hatToDCtx phat) (tM, S.LF.id) ^ 
                             "\n supposed to have type " ^ P.compTypToString cO cD (Whnf.cnormCTyp tau_t) ^ "\n"))

*)
    | (Case (_loc, Ann (Box (_, phat, tR), TypBox (_, tA', cPsi')), branches), (tau, t)) ->
        let _  = LF.check cO cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in 
        let cA = (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in
          (* coverage check here too? -jd *)
          checkBranches (IndexObj (phat, tR)) cO cD cG branches cA (tau, t)

    | (Case (loc, i, branches), (tau, t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypBox (_, tA, cPsi),  t') ->
              begin try Coverage.covers cO cD cG branches (tA, cPsi)
                    with Coverage.NoCover -> (Printf.printf "Coverage checking failed\n";
                                              raise (Error (loc, E.NoCover)))
              end;
              checkBranches DataObj cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau,t)
          | (tau',t') -> raise (Error (loc, E.CompMismatch(cO, cD, cG, i, E.Box, (tau', t'))))
        end

    | (Syn (loc, i), (tau, t)) ->
        let ttau' = (syn cO cD cG i) in 
        if C.convCTyp (tau,t)  ttau' then 
          ()
        else
          raise (Error (loc, E.CompIllTyped (cO, cD, cG, e, (tau,t), ttau')))

    | (If (loc, i, e1, e2), (tau,t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypBool , _ ) -> 
              (check cO cD cG e1 (tau,t) ; 
               check cO cD cG e1 (tau,t) )
          | tau_theta' -> raise (Error (loc, E.CompIfMismatch (cO, cD, cG, tau_theta')))
        end 

  and check cO cD cG e (tau, t) =
    dprint (fun () -> "check cO = " ^ P.octxToString cO);
    checkW cO cD cG e (C.cwhnfCTyp (tau, t));

  and syn cO cD cG e = match e with
    | Var x   -> (lookup cG x, C.m_id)
        (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD !!! *)

    | Const prog ->
        ((Comp.get prog).Comp.typ, C.m_id)

    | Apply (loc , e1, e2) ->
        begin match C.cwhnfCTyp (syn cO cD cG e1) with
          | (TypArr (tau2, tau), t) ->
              check cO cD cG e2 (tau2, t);
              (tau, t)
          | (tau, t) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e1, E.Arrow, (tau,t))))
        end

    | CtxApp (loc, e, cPsi) ->
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypCtxPi ((_psi, w, _ ) , tau), t) ->
              let tau1 = Ctxsub.csub_ctyp cD cPsi 1 (Whnf.cnormCTyp (tau,t)) in
                LF.checkSchema cO cD cPsi (Schema.get_schema w);
                 (* (tau', t') *)
                 (tau1, C.m_id)                
          | (tau, t) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.CtxPi, (tau,t))))
        end
    | MApp (loc, e, (phat, cObj)) ->
        begin match (cObj, C.cwhnfCTyp (syn cO cD cG e)) with
          | (NormObj tM, (TypPiBox ((I.MDecl(_, tA, cPsi), _ ), tau), t)) ->
              LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id);
              (tau, I.MDot(I.MObj (phat, tM), t))

          | (NeutObj h, (TypPiBox ((I.PDecl(_, tA, cPsi), _ ), tau), t)) ->
              let tB = LF.inferHead loc cO cD cPsi h in 
                if Whnf.convTyp (tB, S.LF.id) (C.cnormTyp (tA, t), S.LF.id) then
                  (tau, I.MDot(I.PObj (phat, h), t))
                else 
                  raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.PiBox, (tau,t))))

          | (_ , (tau, t)) -> 
              raise (Error (loc, E.CompMismatch (cO, cD, cG, e, E.PiBox, (tau,t))))
        end

    | Ann (e, tau) ->
        check cO cD cG e (tau, C.m_id);
        (tau, C.m_id)

    | Equal(loc, i1, i2) -> 
         let ttau1 = syn cO cD cG i1 in 
         let ttau2 = syn cO cD cG i2 in            
           if Whnf.convCTyp ttau1 ttau2 then 
             begin match (Whnf.cwhnfCTyp ttau1) with 
               | (TypBox _ , _ ) ->  (TypBool, C.m_id)
               | (TypBool, _ )   ->  (TypBool, C.m_id)
               | _               ->  raise (Error (loc, E.CompEqTyp (cO, cD, ttau1))) 
             end

           else 
             raise (Error(loc, E.CompEqMismatch (cO, cD, ttau1, ttau2 )))

    | Boolean _  -> (TypBool, C.m_id)





  and checkBranches caseTyp cO cD cG branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cO cD cG branch tAbox ttau) branches

(*  and checkBranch _caseTyp cO cD cG branch (tP, cPsi) (tau, t) =
    match branch with
      | BranchBox (cD1,  (cPsi1, (I.Root(loc, _, _ ) as tR1), (t1', cD1')),  e1) ->
          (* By invariant: cD1' |- t1' <= cD, cD1 *)
          let _         = LF.checkMSub cO cD1' t1' (Context.append cD cD1) in  
          let (tP1,s1)  = LF.syn cO cD1 cPsi1 (tR1, S.LF.id)  in 

          (* Apply to the type tP1[Psi1] the refinement substitution t1' *)
          (* cD1 ; cPsi1 |- tM1 <= tA1 
           * cD1'  |- t1' <= cD, cD1  and 
           * cD, cD1 |- MShift (n+n1) . u_n . ... . u₁  <= cD1
           *       t1 = MShift (n+n1) . u_n . ... . u₁  
           *) 
          let n1  = length cD1 in 
          let n   = length cD  in 
          let t1  =  Whnf.mvar_dot (I.MShift n) cD1 in   
          (* cD1' |- t1_b <= cD1  where t1_b is the refinement substitution we apply to the pattern 
                                  and its context and type
           *)
          let t1_b      = Whnf.mcomp t1 t1' in 
          (* cD1'          |- cPsi1' ctx   where cPsi1' is the context of the pattern *)
          (* cD1' ; cPsi1' |- sP1' <- type  where sP1'  is the type of the pattern    *)
          let sP1'      = (Whnf.cnormTyp (tP1, t1_b), Whnf.cnormSub (s1, t1_b)) in 
          let cPsi1'    = Whnf.cnormDCtx (cPsi1, t1_b) in  

          (* Apply to the type of the scrutinee tP[Psi] the refinement substitution t1' *)
          (* cD |- cPsi ctx  and cD, cD1 |- MShift n1 <= cD
           *                 and cD1'    |- t1'       <= cD, CD1
           *               then  cD1' |- t1'' <= cD
           *)
          let t1''  = Whnf.mcomp (I.MShift n1) t1' in 
          let cPsi' = Whnf.cnormDCtx (cPsi, t1'') in  
          let tP'   = Whnf.cnormTyp (tP, t1'') in 

          (* Verify that the refinement substitution t1' 
           * makes the type of the pattern equal to the type of the scrutinee 
           * 
           * and cD1' |- |[t1'']|cPsi = |[t1]|cPs1
           * and cD1' ; |[t1]|cPsi1 |-  |[t1]|tP1 <= type
           * and cD1' ; |[t1]|cPsi1 |- |[t1]|tP1 = |[t1'']|tP
           *)

          let  _    = (if Whnf.convDCtx cPsi1' cPsi'
                         && Whnf.convTyp sP1' (tP', S.LF.id)
                       then  ()
                       else raise (Error (loc, E.CompPattMismatch ((cO, cD1, cPsi1, tR1, (tP1,s1)), 
                                                                   (cO, cD, cPsi, (tP, S.LF.id)))))) in 

          (* let t' = Whnf.mvar_dot t cD1 in  
             let t''  = Whnf.mcomp t' t1'' in *)
          (* if cD |- t <= cD0 then
             cD, cD1 |- t' <= cD0, cD1  *)


          let cG' = Whnf.cnormCtx (cG, t1'') in 
          let t'' = Whnf.mcomp t t1'' in

          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.mctxToString cO cD1 ^ " . " ^ 
                        P.normalToString cO cD1 cPsi1 (tR1, S.LF.id) ^ "\n   =>  " ^ 
                            P.expChkToString cO cD1' cG' e1 ^ 
                            "\n has type "  ^ P.compTypToString cO cD1' (Whnf.cnormCTyp (tau, t'')) ^ "\n" 
                       ) in
                 
          in
            check cO cD1' cG' e1 (tau, t'');
*)
  and checkBranch _caseTyp cO cD cG branch (tP, cPsi) (tau, t) =
    match branch with
      | BranchBox (cO1', cD1',  (_cPsi1, (I.Root(loc, _, _ ) as tR1), t1, cs),  e1) ->
          (* By invariant: cD1' |- t1 <= cD *)
          let _     = LF.checkMSub cO1' cD1' t1 (Ctxsub.ctxnorm_mctx (cD,cs)) in  
          let tP1   = Ctxsub.ctxnorm_typ (Whnf.cnormTyp (tP, t1), cs) in 
          let cPsi1 = Ctxsub.ctxnorm_dctx (Whnf.cnormDCtx (cPsi, t1), cs) in

          let _  = LF.check cO1' cD1' cPsi1 (tR1, S.LF.id)  (tP1, S.LF.id) in 


          let cG' = Whnf.cnormCtx (Ctxsub.ctxnorm_gctx (cG, cs), t1) in 
          let t'' = Whnf.mcomp t t1 in

          let tau  = Whnf.cnormCTyp (tau, t'') in
          let tau' = Ctxsub.ctxnorm_ctyp (tau, cs) in
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.octxToString cO1' ^ " ; \n" ^ 
                        P.mctxToString cO1' cD1' ^ " ;\n " ^ 
                        P.normalToString cO1' cD1' cPsi1 (tR1, S.LF.id) ^ "\n   =>  " ^ 
                            P.expChkToString cO1' cD1' cG' e1 ^ 
                            "\n has type "  ^ P.compTypToString cO1' cD1' tau' ^ "\n" 
                       )
          in

            check cO1' cD1' cG' e1 (tau', Whnf.m_id)

end
  


module Sgn = struct

  let rec check_sgn_decls = function
    | [] ->
        ()

    | Syntax.Int.Sgn.Typ (_a, tK) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkKind cO cD cPsi tK;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Const (_c, tA) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkTyp cO cD cPsi (tA, Substitution.LF.id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Schema (_w, schema) :: decls ->
        let cD   = Syntax.Int.LF.Empty in
        let cO   = Syntax.Int.LF.Empty in
        let cPsi = Syntax.Int.LF.Null in
          LF.checkSchema cO cD cPsi schema;
          check_sgn_decls decls

    | Syntax.Int.Sgn.Rec (_f, tau, e) :: decls ->
        let cD = Syntax.Int.LF.Empty in
        let cO = Syntax.Int.LF.Empty in
        let cG = Syntax.Int.LF.Empty in
          Comp.checkTyp cO cD tau;
          Comp.check cO cD cG e (tau, Whnf.m_id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Pragma (_a) :: decls ->
        check_sgn_decls decls

end
