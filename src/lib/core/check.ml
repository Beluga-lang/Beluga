(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Brigitte Pientka
   modified: Joshua Dunfield

*)


module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [3])


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
  in
    Dot (front, s)

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

    | ((Root (loc, h, tS), s (* id *)),   (Atom _, _s')) ->
        (* cD ; cPsi |- [s]tA <= type  where sA = [s]tA *)
        let sA' = Whnf.whnfTyp (inferHead cO cD cPsi h, LF.id) in
          begin try
            let sP = synSpine cO cD cPsi (tS, s) sA' in
              if not (Whnf.convTyp sP sA) then
                raise (Error (loc, TypMismatch (cO, cD, cPsi, sM, sA, sP)))
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
  and lookupCtxVar = function
    | Empty -> raise (Violation ("Context variable not found"))
    | Dec (cO, CDecl (psi, schemaName)) -> function
        | CtxName phi when psi = phi -> (psi, schemaName)
        | (CtxName _phi) as ctx_var  -> lookupCtxVar cO ctx_var
        | CtxOffset 1                -> (psi, schemaName)
        | CtxOffset n                -> lookupCtxVar cO (CtxOffset (n - 1))

  and lookupCtxVarSchema cO phi = snd (lookupCtxVar cO phi)

  (* inferHead cO cD cPsi h = tA
   *
   * Invariant:
   *
   * returns tA if
   * cO cD ; cPsi |- h => tA
   * where cO cD ; cPsi |- tA <= type
   * else exception Error is raised.
   *)
  and inferHead cO cD cPsi head = match head with
    | BVar k' ->
        let (_, _l) = dctxToHat cPsi in
        let TypDecl (_, tA) = ctxDec cPsi k' in
          tA
    
    | Proj (tuple_head, target) ->
        let srecA = match tuple_head with
          | BVar k' ->
              let TypDecl (_, Sigma recA) = ctxSigmaDec cPsi k' in
                (recA, LF.id)
          | PVar (Offset p, s) ->
              begin let (tTuple, cPsi') = Cwhnf.mctxPDec cD p in
                checkSub cO cD cPsi s cPsi';
                match tTuple with
                    Sigma recA -> (recA, s)
              end
        in
          TClo (getType tuple_head srecA target 1)
    
    | Const c ->
        (Term.get c).Term.typ
    
    | MVar (Offset u, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (tA, cPsi') = Cwhnf.mctxMDec cD u in
          checkSub cO cD cPsi s cPsi' ;
          TClo (tA, s)
    
    | PVar (Offset p, s) ->
        (* cD ; cPsi' |- tA <= type *)
        let (tA, cPsi') = Cwhnf.mctxPDec cD p in
          checkSub cO cD cPsi s cPsi' ;
          dprint (fun () -> "check: cPsi' (context of pvar)    = " ^ P.dctxToString cO cD cPsi') ;
          dprint (fun () -> "check:  cPsi (context in pattern) = " ^ P.dctxToString cO cD cPsi) ;
          dprint (fun () -> "check: synthesizing " ^ P.typToString cO cD cPsi (tA, s) ^ " for PVar") ;
          
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
          begin let (Schema elems) as schema = Schema.get_schema (lookupCtxVarSchema cO ctx_var) in
            try let _ = checkTypeAgainstSchema cO cD Null (TClo sA) schema elems in
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

  (* checkSub cO cD cPsi s cPsi' = ()
   *
   * Invariant:
   *
   * succeeds iff cO cD ; cPsi |- s : cPsi'
   *)
  and checkSub cO cD cPsi s cPsi' = match (cPsi, s, cPsi') with
    | (Null, Shift (NoCtxShift, 0), Null) ->
        ()

    | (CtxVar psi, Shift (NoCtxShift, 0), CtxVar psi')  ->
        if psi = psi' then
          ()
        else
          raise (Violation "Context variable mismatch")
            (* (CtxVarMisMatch (psi, psi')) *)

    | (CtxVar psi, Shift (CtxShift (psi'), 0), Null) ->
        if psi = psi' then
          ()
        else
          raise (Error (None, SubIllTyped))

    | (Null, Shift (NegCtxShift (psi'), 0), CtxVar psi) ->
        if psi = psi' then
          ()
        else
          raise (Error (None, SubIllTyped))

    (* SVar case to be added - bp *)

    | (DDec (cPsi, _tX),  Shift (psi, k),  Null) ->
        if k > 0 then
          checkSub cO cD cPsi (Shift (psi, k - 1)) Null
        else
          raise (Error (None, SubIllTyped))

    | (DDec (cPsi, _tX),  Shift (phi, k),  CtxVar psi) ->
        if k > 0 then
          checkSub cO cD cPsi (Shift (phi, k - 1)) (CtxVar psi)
        else
          raise (Violation ("Substitution ill-typed: k = %s" ^ (string_of_int k)))
          (* (SubIllTyped) *)

    | (cPsi',  Shift (psi, k),  cPsi) ->
        checkSub cO cD cPsi' (Dot (Head (BVar (k + 1)), Shift (psi, k + 1))) cPsi

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
        (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
        let _   = checkSub cO cD cPsi' s' cPsi
          (* ensures that s' is well-typed before comparing types tA1 =[s']tA2 *)
        and tA1 = inferHead cO cD cPsi' h in
          if Whnf.convTyp (tA1, LF.id) (tA2, s') then
            ()
          else
            let _ = Printf.printf " Inferred type: %s\n Expected type: %s\n\n"
              (P.typToString cO cD cPsi (tA1, LF.id))
              (P.typToString cO cD cPsi (tA2, s')) in
              raise (Error (None, SubIllTyped))
                (* let sM = Root (None, h, Nil) in
                   raise (TypMismatch (cPsi', sM, (tA2, s'), (tA1, LF.id)))
                *)

    | (cPsi',  Dot (Obj tM, s'),  DDec (cPsi, TypDecl (_, tA2))) ->
        (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
        let _ = checkSub cO cD cPsi' s' cPsi in
          (* ensures that s' is well-typed and [s']tA2 is well-defined *)
          check cO cD cPsi' (tM, LF.id) (tA2, s')

    | (cPsi1,  s,  cPsi2) ->
        Printf.printf "\n Check substitution: %s   |-    %s    <= %s  \n\n"
          (P.dctxToString cO cD cPsi1)
          (P.subToString cO cD cPsi1 s)
          (P.dctxToString cO cD cPsi2);
        raise (Violation "Substitution is ill-typed; this case should be impossible.\n")

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
  and checkTyp' cO cD cPsi (tA, s) = match tA with
    | Atom (loc, a, tS) ->
        (* FIXME -bp *)
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

    | CtxVar (CtxOffset psi_offset)  ->
        if psi_offset <= (Context.length cO) then
          ()
        else
          raise (Violation "Context variable out of scope")

(* other cases should be impossible -bp *)


  and projectCtxIntoDctx = function
    | Empty -> Null
    | Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

 (* checkTypeAgainstSchema cO cD cPsi tA sch (elements : sch_elem list)
  *   sch = full schema, for error messages
  *   elements = elements to be tried
  *)
  and checkTypeAgainstSchema cO cD cPsi tA sch elements =
    (* if tA is not a Sigma, "promote" it to a one-element typRec *)
    let _ = dprint (fun () ->
                      "checkTypeAgainstSchema "
                    ^ P.typToString cO cD cPsi (tA, LF.id)
                    ^ "  against  "
                    ^ P.schemaToString (Schema elements)) in
    in
      match elements with
        | [] -> 
            raise (Violation ("Type " ^ P.typToString cO cD cPsi (tA, LF.id) ^ " doesn't check against schema " ^ P.schemaToString sch))
        | element :: elements ->
            try
              checkTypeAgainstElement cO cD cPsi (tA, LF.id) element
            with 
              | (Match_failure _) as exn -> raise exn
              | _ -> checkTypeAgainstSchema cO cD cPsi tA sch elements

  and checkTypeAgainstElement cO cD cPsi (tA, s) (SchElem (some_part, block_part)) = 
    let tArec = match tA with
      | Sigma tArec -> tArec
      | nonsigma -> SigmaLast nonsigma in
    let dctx        = projectCtxIntoDctx some_part in
    let dctxSub     = ctxToSub dctx in
    let _ = dprint (fun () -> "checkTypeAgainstElement  "
                      ^ P.typToString cO cD cPsi (tA, s)
                      ^ "  against  "
                      ^ P.typRecToString cO cD cPsi (block_part, dctxSub)) in
(*    let _           = dprint (fun () -> "checkTypeAgainstElement  " ^ P.subToString cO cD cPsi dctxSub) in *)
    let phat        = dctxToHat cPsi in
      begin
        dprint (fun () -> "***Unify.unifyTypRec ("
                        ^ "\n   dctx = " ^ P.dctxToString cO cD dctx
                        ^ "\n   " ^ P.typToString cO cD cPsi (tA, s)
                        ^ "\n== " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) );
        try
          (* Unify.unifyTyp cD (phat, (normedA, LF.id), (normedElem1, dctxSub)) *)
          Unify.unifyTypRec cD (phat, (tArec, LF.id), (block_part, dctxSub))
        ; dprint (fun () -> "checkTypeAgainstElement\n"
                            ^ "  block_part = " ^ P.typRecToString cO cD cPsi (block_part, dctxSub) ^ "\n"
                            ^ "  succeeded.")
        ; (block_part, dctxSub)
        with (Unify.Unify _) as exn ->
          dprint (fun () -> "Type " 
                    ^ P.typToString cO cD cPsi (tA, LF.id) ^ " doesn't unify with " 
                    ^ P.typRecToString cO cD cPsi (block_part, dctxSub));
          raise exn
      end
  
  and checkTypeAgainstElementProjection cO cD cPsi (tA, s) (head, k) (SchElem (some_part, block_part)) = 
    let kth_element_of_block_part (* : tclo *) = getType head (block_part, LF.id) k 1 in
    let kth_element_of_schelem = SchElem (some_part, SigmaLast (TClo kth_element_of_block_part)) in
    let (_kth_element_inst, subst) =
      checkTypeAgainstElement cO cD cPsi (tA, s) kth_element_of_schelem
    in
      (block_part, subst)

(****
  and checkTypRecAgainstSchema cO cD cPsi typRec sch =
    let rec projectCtxIntoDctx = function
      |  Empty -> Null
      |  Dec (rest, last) -> DDec (projectCtxIntoDctx rest, last)

    and checkTypeAgainstElement (SchElem (some_part, block_part)) =
      match (some_part, block_part) with
          (cSomeCtx, sigma) ->
            let dctx = projectCtxIntoDctx cSomeCtx in 
            let dctxSub = ctxToSub dctx in
            let _ = dprint (fun () -> "TypRec:checkTypeAgainstElement  " ^ P.subToString cO cD dctx dctxSub) in

            let phat = dctxToHat cPsi in
              dprint (fun () -> "***Unify.unifyTypRec (" ^ "\n   dctx = " 
                        ^ P.dctxToString cO cD dctx ^ "\n   " 
                        ^ P.typRecToString cO cD cPsi (typRec, LF.id) ^"\n== " 
                        ^ P.typRecToString cO cD cPsi (sigma, dctxSub) );
              try
                Unify.unifyTypRec cD (phat, (typRec, LF.id), (sigma, dctxSub))
              with exn ->  
                dprint (fun () -> "TypRec " 
                          ^ P.typRecToString cO cD cPsi (typRec, LF.id) ^ " doesn't unify with " 
                          ^ P.typRecToString cO cD cPsi (sigma, dctxSub));
                raise exn
    in
      function
        | [] -> 
            raise (Violation ("TypRec " 
                          ^ P.typRecToString cO cD cPsi (typRec, LF.id) ^ " doesn't check against schema " 
                          ^ P.schemaToString sch))

        | element :: elements ->
            try
              checkTypeAgainstElement element
            with _ ->
              checkTypRecAgainstSchema cO cD cPsi typRec sch elements
*****)

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
      Whnf.convSchElem elem1 elem2 (* (cSome1 = cSome2) && (block1 = block2)  *) in
    let _ = dprint (fun () -> "checkElementAgainstElement "
                      ^ P.schemaToString (Schema[elem1])
                      ^ " <== "
                      ^ P.schemaToString (Schema[elem2])
                      ^ ":  "
                      ^ string_of_bool result)
    in result

  (* checkElementAgainstSchema cO cD sch_elem (elements : sch_elem list) *)
  and checkElementAgainstSchema cO cD sch_elem elements =
    List.exists (checkElementAgainstElement cO cD sch_elem) elements

  and checkSchema cO cD cPsi (Schema elements as schema) =
    dprint (fun () -> "checkSchema " ^ P.octxToString cO ^ " ... " 
              ^ P.dctxToString cO cD cPsi ^ " against " ^ P.schemaToString schema);
    print_string " WARNING: Schema checking not fully implemented\n";
    match cPsi with
      | Null -> ()
      | CtxVar phi ->
          let Schema phiSchemaElements = Schema.get_schema (lookupCtxVarSchema cO phi) in
            if not (List.for_all (fun phiElem -> checkElementAgainstSchema cO cD phiElem elements) phiSchemaElements) then
              raise (Error (None, CtxVarMismatch (cO, phi, schema)))
      | DDec (cPsi', decl) ->
          begin
            checkSchema cO cD cPsi' schema
          ; match decl with
              | TypDecl (_x, tA) ->
                  let _ = checkTypeAgainstSchema cO cD cPsi' tA schema elements in ()
          end

end (* struct LF *)

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
  module C = Cwhnf

  module P = Pretty.Int.DefaultPrinter

  type caseType  = IndexObj of I.psi_hat * I.normal | DataObj 

  (*  module Unif = Unify.UnifyNoTrail *)

  exception Violation of string
  exception Error of E.error

  let rec length cD = match cD with
    | I.Empty -> 0
    | I.Dec(cD, _) -> 1 + length cD

  let rec lookup cG k = match (cG, k) with
    | (I.Dec (_cG', CTypDecl (_,  tau)), 1) -> tau
    | (I.Dec ( cG', CTypDecl (_, _tau)), k) ->
        lookup cG' (k - 1)

  let rec split tc d = match (tc, d) with
    | (tc, 0) -> tc
    | (MDot (_ft, t), d) -> split t (d - 1)

  let rec mctxToMSub cD = match cD with
    | I.Empty -> 
        C.id

    | I.Dec (cD', I.MDecl(_, tA, cPsi)) ->
        let t     = mctxToMSub cD' in
        let cPsi' = Cwhnf.cnormDCtx (cPsi, t) in
        let tA'   = Cwhnf.cnormTyp (tA, t) in
        let u     = Whnf.newMVar (cPsi', tA') in
        let phat  = Context.dctxToHat cPsi in
          MDot (MObj (phat, I.Root (None, I.MVar (u, S.LF.id), I.Nil)), t)

    | I.Dec (cD', I.PDecl(_, tA, cPsi)) ->
        let t    = mctxToMSub cD' in
        let p    = Whnf.newPVar (Cwhnf.cnormDCtx (cPsi, t),  Cwhnf.cnormTyp (tA, t)) in
        let phat = Context.dctxToHat cPsi in
          MDot (PObj (phat, I.PVar (p, S.LF.id)), t)

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
      | MShift 0     -> t1
      | MDot (ft, t) -> MDot (ft, ext t)
      (* other cases should be impossible *)
    in ext t2

  let rec checkTyp cO cD tau = match tau with
    | TypBox (tA, cPsi) ->
        LF.checkDCtx cO cD cPsi;
        LF.checkTyp  cO cD cPsi (tA, S.LF.id)

    | TypArr (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2

    | TypCross (tau1, tau2) ->
        checkTyp cO cD tau1;
        checkTyp cO cD tau2

    | TypCtxPi ((psi_name, schema_cid), tau) ->
        checkTyp (I.Dec (cO, I.CDecl (psi_name, schema_cid))) cD tau

    | TypPiBox ((cdecl, _), tau) ->
        checkTyp cO (I.Dec (cD, cdecl)) tau


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
  let rec checkW cO cD cG e ttau = match (e , ttau) with
    | (Rec (f, e), (tau, t)) ->
        check cO cD (I.Dec (cG, CTypDecl (f, TypClo (tau,t)))) e ttau

    | (Fun (x, e), (TypArr (tau1, tau2), t)) ->
        check cO cD (I.Dec (cG, CTypDecl (x, TypClo(tau1, t)))) e (tau2, t)

    | (CtxFun (psi, e) , (TypCtxPi ((_psi, schema), tau), t)) ->
        check (I.Dec(cO, I.CDecl(psi, schema))) cD cG e (tau, t)

    | (MLam (u, e), (TypPiBox ((I.MDecl(_u, tA, cPsi), _), tau), t)) ->
        check cO (I.Dec(cD, I.MDecl(u, C.cnormTyp (tA, t), C.cnormDCtx (cPsi, t))))
          cG   e (tau, C.mvar_dot1 t)

    | (Pair (e1, e2), (TypCross (tau1, tau2), t)) ->
        check cO cD cG e1 (tau1, t);
        check cO cD cG e2 (tau2, t)

    | (LetPair (i, (x, y, e)), (tau, t)) ->
        begin match C.cwhnfCTyp (syn cO cD cG i) with
          | (TypCross (tau1, tau2), t') ->
              let cG' = I.Dec (I.Dec (cG, CTypDecl (x, TypClo (tau1, t'))), CTypDecl (y, TypClo(tau2, t'))) in
                check cO cD cG' e (tau,t)
          | _ -> raise (Violation "Case scrutinee not of boxed type")
        end

    | (Box (_phat, tM), (TypBox (tA, cPsi), t)) ->
        begin try
          let cPsi' = C.cnormDCtx (cPsi, t) in
          let tA'   = C.cnormTyp (tA, t) in
            LF.check cO cD  cPsi' (tM, S.LF.id) (tA', S.LF.id)
        with Cwhnf.FreeMVar (I.FMVar (u, _ )) ->
          raise (Violation ("Free meta-variable " ^ (R.render_name u)))
        end


    | (Case (Ann (Box (phat, tR), TypBox (tA', cPsi')), branches), (tau, t)) ->
        let _  = LF.check cO cD  cPsi' (tR, S.LF.id) (tA', S.LF.id) in 
        let cA = (Whnf.normTyp (tA', S.LF.id), Whnf.normDCtx cPsi') in 
          checkBranches (IndexObj (phat, tR)) cO cD cG branches cA (tau, t) 

    | (Case (e, branches), (tau, t)) -> 
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypBox (tA, cPsi),  t') -> 
              checkBranches DataObj cO cD cG branches (C.cnormTyp (tA, t'), C.cnormDCtx (cPsi, t')) (tau,t)
          | _ -> raise (Violation "Case scrutinee not of boxed type")
        end

    | (Syn e, (tau, t)) ->
        if C.convCTyp (tau,t) (syn cO cD cG e) then 
          ()
        else
          raise (Violation "Type mismatch")

  and check cO cD cG e (tau, t) =
    dprint (fun () -> "check cO = " ^ P.octxToString cO);
    checkW cO cD cG e (C.cwhnfCTyp (tau, t))

  and syn cO cD cG e = match e with
    | Var x  -> (lookup cG x, C.id)
        (* !!!! MAY BE WRONG since only . |- ^0 : .   and not cD |- ^0 : cD !!! *)

    | Const prog ->
        ((Comp.get prog).Comp.typ, C.id)

    | Apply (e1, e2) ->
        begin match C.cwhnfCTyp (syn cO cD cG e1) with
          | (TypArr (tau2, tau), t) ->
              check cO cD cG e2 (tau2, t);
              (tau, t)
          | _ -> 
              raise (Violation "Function mismatch")
        end

    | CtxApp (e, cPsi) ->
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypCtxPi ((_psi, w) , tau), t) ->
              let tau1 = Cwhnf.csub_ctyp cPsi 1 (Cwhnf.cnormCTyp (tau,t)) in
                LF.checkSchema cO cD cPsi (Schema.get_schema w);
                 (* (tau', t') *)
                 (tau1, Cwhnf.id)                
          | _ -> 
              raise (Violation "Context abstraction mismatch")
        end
    | MApp (e, (phat, tM)) ->
        begin match C.cwhnfCTyp (syn cO cD cG e) with
          | (TypPiBox ((I.MDecl(_, tA, cPsi), _ ), tau), t) ->
              LF.check cO cD (C.cnormDCtx (cPsi, t)) (tM, S.LF.id) (C.cnormTyp (tA, t), S.LF.id);
              (tau, MDot(MObj (phat, tM), t))
          | _ -> raise (Violation "MLam mismatch")
        end

    | (Ann (e, tau)) ->
        check cO cD cG e (tau, C.id);
        (tau, C.id)

  and checkBranches caseTyp cO cD cG branches tAbox ttau =
    List.iter (fun branch -> checkBranch caseTyp cO cD cG branch tAbox ttau) branches

  and checkBranch caseTyp cO cD cG branch (tA, cPsi) (tau, t) =
    match branch with
      | BranchBox (cD1,  (_phat, tM1, (tA1, cPsi1)),  e1) ->

          LF.check cO cD1 cPsi1 (tM1, S.LF.id) (tA1, S.LF.id);
                                         (* cD |- t <= cD0 *)
          let _ = dprint (fun () -> "\nCheckBranch with pattern\n Pi " ^
                        P.mctxToString cO cD1 ^ " . " ^ 
                        P.normalToString cO cD1 cPsi1 (tM1, S.LF.id) ^ " : " ^ 
                        P.typToString cO cD1 cPsi1 (tA1, S.LF.id) ^ "[" ^ 
                            P.dctxToString cO cD1 cPsi1 ^ "]\n   =>  " ^ 
                            P.expChkToString cO (Context.append cD cD1) cG e1 ^ 
                            "\n has type "  ^ P.compTypToString cO cD (Cwhnf.cnormCTyp (tau,t)) ^ "\n" 
                       ) in

          let d1   = length cD1 in
          let _d   = length cD in
          let t1   = mctxToMSub cD1 in   (* {cD1} |- t1 <= cD1 *)
          let t'   = mctxToMSub cD in    (* {cD}  |- t' <= cD *)
          let tc   = extend t' t1 in     (* {cD1, cD} |- t', t1 <= cD, cD1 *)
          let phat = dctxToHat cPsi in

          let cPsi1' = C.cnormDCtx (cPsi1, t1) in 
          let tA1'   = C.cnormTyp (tA1, t1) in 
          let tM1'   = C.cnorm (tM1, t1) in  

          let cPsi'  = C.cnormDCtx (cPsi, t') in 
          let tA'    = C.cnormTyp (tA, t') in 

          let _  = 
            begin match caseTyp with
              | IndexObj (_phat, tM') -> 
                  begin try
                    Unify.unify cD1 (phat, (C.cnorm (tM', t'), S.LF.id), (tM1, S.LF.id)) 
                  with Unify.Unify msg -> 
                    Printf.printf "Unify ERROR: %s \n"  msg;
                    raise (Violation "Pattern matching on index argument failed") 
                  end
              | DataObj -> ()
            end
          in

(*          let _    = Unify.unifyDCtx (I.Empty)
            (C.cnormDCtx (cPsi, t')) (C.cnormDCtx (cPsi1, tc)) in
          let _    = Unify.unifyTyp (I.Empty)
            (phat, (C.cnormTyp (tA, t'), S.LF.id), (C.cnormTyp (tA1, tc), S.LF.id))  in
*)
          let _    = Unify.unifyDCtx (I.Empty) cPsi' cPsi1' in
          let _    = Unify.unifyTyp (I.Empty)  (phat, (tA', S.LF.id), (tA1', S.LF.id))  in

        let _ = dprint (fun () -> "\nCheckBranch with pattern (after unification) \n  " ) in 
        let _ = dprint (fun () -> 
                        (P.normalToString cO I.Empty cPsi1' (tM1', S.LF.id)) ^ " : " ^ 
                        (P.typToString cO I.Empty cPsi1' (tA1', S.LF.id)) ^ "[" ^ 
                        (P.dctxToString cO I.Empty cPsi1') ^ "] \n   =>  ... \n\n " 
                       ) in


          let (tc', cD1'') = Abstract.abstractMSub tc in  (* cD1' |- tc' <= cD, cD1 *)

          let _ = dprint (fun () -> "Show     tc' = " ^ P.msubToString cO cD1'' tc') in 
          let _ = dprint (fun () -> "Show   cD1'' = " ^ P.mctxToString cO cD1'') in 
          let _ = dprint (fun () -> "Show cD, cD1 = " ^ P.mctxToString cO (Context.append cD cD1)) in 
          let _ = dprint (fun () -> "Show      e1 = " ^ P.expChkToString cO (Context.append cD cD1) cG e1) in 
          let t'' = split tc' d1 in (* cD1' |- t'' <= cD  suffix *) 
            (*
          let cPsi_n = Cwhnf.cnormDCtx (cPsi, t'') in  
          let cPsi1_n = Cwhnf.cnormDCtx (cPsi1, tc') in  
          let  _   = Printf.printf "Type of scrutinee: %s   |-    %s \n\n Type of Pattern in branch: %s   |-  %s \n\n"
            (P.dctxToString cO cD cPsi_n)
            (P.typToString  cO cD cPsi_n (Cwhnf.cnormTyp (tA, t'')))
            (P.dctxToString cO cD cPsi1_n)
            (P.typToString  cO cD cPsi1_n (Cwhnf.cnormTyp (tA1, tc'))) in 
            *)
          let e1' = 
            begin try
              Cwhnf.cnormExp (e1, tc')
            with Cwhnf.FreeMVar (I.FMVar (u, _)) ->
              raise (Violation ("Encountered free meta-variable " ^ (R.render_name u)))
            end
          in
          let cG1 = C.cwhnfCtx (cG, t'') in
          let _ = dprint (fun () -> "Show     e1' = " ^ P.expChkToString cO cD1'' cG1 e1') in 
          let tau' = (tau, C.mcomp t t'') in
          let _ = dprint (fun () -> "\nCheckBranch body\n" ^ " " ^
                        P.mctxToString cO cD1'' ^ "  |-  " ^
                        P.expChkToString cO cD1'' cG1 e1' ^ " : " ^ 
                        P.compTypToString cO cD1'' (Cwhnf.cnormCTyp tau') ^ "\n" 
                       ) in

            check cO cD1'' cG1 e1' tau'
  
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
          Comp.check cO cD cG e (tau, Cwhnf.id);
          check_sgn_decls decls

    | Syntax.Int.Sgn.Pragma (_a, ) :: decls ->
        check_sgn_decls decls

end
