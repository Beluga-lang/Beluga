(** Coverage checker

   @author Joshua Dunfield
*)

open Syntax.Int
open Syntax.Int.Comp

module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module U = Unify.EmptyTrail   (* is EmptyTrail the right one to use?  -jd *)
module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [29])

let covby_counter = ref 0


(* why doesn't ocaml have List.tabulate? *)
(* tabulate : int -> (int -> 'a) -> 'a list
 *
 * tabulate n f = [f(0); f(1); ...; f(n -1)]
 *)
let tabulate n f =
  let rec tabulate n acc =
    if n <= 0 then acc
    else tabulate (n - 1) (f(n - 1) :: acc)
  in
    tabulate n []

(* range : int -> (int -> unit) -> unit
 *
 * range n f  equivalent to  (f(0); f(1); ...; f(n -1))
 *)
let range n (f : int -> unit) =
  let _ = tabulate n f in
    ()

(* tryList : ('a -> 'b) -> 'a list -> 'b
 *
 * tryList f xs = f(x) for the first x in xs for which f returns a value;
 * otherwise, raises the last exception raised by f.
 *
 * Precondition: xs non-nil
 *)
let rec tryList f = function
    | [last] -> f last
    | first :: rest -> (try f first with Match_failure (s, x, y) -> raise (Match_failure (s, x, y))
                                       | _ -> tryList f rest)
    | [] -> (dprnt ("tryList precondition violated");
             raise (Match_failure ("", 0, 0)))


let cctxToCSub = Opsem.cctxToCSub
let mctxToMSub = Ctxsub.mctxToMSub


(*
 * type shifter  ---Shifter
 *
 * Shifter passed into the continuation, to fix indices in things created
 * before Delta was extended.
 *)
type shifter = {
  n : int
}

type 'a hanger = HANGER of (shifter -> 'a)

(*
  head : LF.head -> LF.head;
  spine : LF.spine -> LF.spine;
  normal : LF.normal -> LF.normal;
  typ : LF.typ -> LF.typ
*)

let noop_shift = {
  n = 0
}


let hang shiftFn shifter thing =
  HANGER (fun laterShifter -> shiftFn thing (laterShifter.n - shifter.n))
let hang = (hang : ('a -> int -> 'a) -> shifter -> 'a -> 'a hanger)

let hangHead = hang Whnf.mshiftHead
let hangSpine = hang Whnf.mshiftSpine
let hangNormal = hang Whnf.mshiftTerm
let hangTyp = hang Whnf.mshiftTyp
let hangDCtx = hang Whnf.mshiftDCtx

let cut (HANGER f) laterShifter = f laterShifter

let cut = (cut : 'a hanger -> shifter -> 'a)



(*
let bump_shift n shift =
  {head = (fun h -> Whnf.mshiftHead (shift.head h) n);
   spine = (fun spine -> Whnf.mshiftSpine (shift.spine spine) n);
   normal = (fun tM -> Whnf.mshiftTerm (shift.normal tM) n);
   typ = (fun t -> Whnf.mshiftTyp (shift.typ t) n)
  }
*)
let bump_shift increment shifter = {n = shifter.n + increment}


(*
 * type strategy  ---Coverage strategy
 *
 * This type represents the strategy (or the state of the strategy) to use.
 * Currently, this just has a `depth'.
 *)
type strategy = {
  depth : int
}

let strategyToString s = "{" ^ "depth = " ^ string_of_int s.depth ^ "}"

let naive_strategy depth = {depth = depth}
let decrement_depth = function {depth = d} -> {depth = d - 1}

let split_switch strategy (split, noSplit) =
  let shouldSplit strategy = strategy.depth > 0 in
    if shouldSplit strategy then
     (let strategyInSplit = strategy in
        split strategyInSplit)
    else
      (let strategyInNoSplit = strategy in
        noSplit strategyInNoSplit)


exception NoCover

let enableCoverage = ref false
let warningOnly = ref false
let no_covers = ref 0


(* Generating names for Obj-no-split (MVars) *)
let counter = ref 0
let new_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (String.uppercase string ^ string_of_int !counter))



let emptySub = Substitution.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)
let emptyMSub = Whnf.m_id


(* getConstructorsAndTypes : Id.cid_typ -> (Id.cid_term * LF.typ) list
 *
 * Given a type (e.g. nat), return the type's constructors along with their types
 * (e.g. [(z, nat), (suc, nat -> nat)])
 *)
let getConstructorsAndTypes a =
  let constructors = (Types.get a).Types.constructors in
  (* Reverse the list so coverage will be checked in the order that the
     constructors were declared, which is more natural to the user *)
  let constructors = List.rev constructors in   
  let addType c = (c, (Constructors.get c).Constructors.typ) in
    List.map addType constructors

(* dprintCTs
 * Print the list of constructors and types (just for debugging)
 *)
let rec dprintCTs cO cD cPsi = function
        | [] -> dprnt "[end of constructor list]"
        | (c, cSig) :: rest ->
             (dprnt ("\"" ^ R.render_name (Constructors.get c).Constructors.name ^ "\""
                   ^ " : " ^ P.typToString cO cD cPsi (cSig, emptySub));
              dprintCTs cO cD cPsi rest)


(* getConcretesAndTypes : LF.dctx -> (LF.head * LF.typ) list
 *
 * Given a type (e.g. nat), return the type's constructors along with their types
 * (e.g. [(z, nat), (suc, nat -> nat)])
 *)
let getConcretesAndTypes cPsi =
  let rec inner n = function
    | LF.Null -> []
    | LF.CtxVar _ -> []
    | LF.DDec (cPsi, LF.TypDecl(x, tA)) -> (LF.BVar n, tA) :: inner (n+1) cPsi
  in
    List.rev (inner 1 cPsi)


(* getParameterSchemaElems : LF.mctx -> LF.dctx -> LF.sch_elem list
 * getParameterSchemaElems cO cPsi
 *    = [F_1, ..., F_n]   if cPsi has a context variable of schema F_1 + ... + F_n
 *    = []                if cPsi has no context variable
 *)
let getParameterSchemaElems cO cPsi = 
  match Context.ctxVar cPsi with
    | None -> []
    | Some psi ->
        let LF.Schema elems = Store.Cid.Schema.get_schema (Context.lookupCtxVarSchema cO psi) in 
          elems

let rec lenTypRec = function
  | LF.SigmaLast _ -> 1
  | LF.SigmaElem (_x, _tA, typRec) -> 1 + lenTypRec typRec
  
let rec iterTypRec f (head, s_recA) =
  let typRec = Whnf.normTypRec s_recA in
(*  let _ = dprint (fun () -> "iterTypRec>>> " ^ string_of_int (lenTypRec typRec)) in *)
  let len = lenTypRec typRec in
    range
      len
      (fun m ->
         let m = len - m in  (* range counts down, but it's more intuitive to start from 0 *)
         let _ = dprint (fun () -> "iterTypRec>>> m = " ^ string_of_int m ^ " (len = " ^string_of_int len ^ ")") in
         let sA = LF.getType head (typRec, emptySub) m 1 in
           f (sA, m))

let iterTypRec = (iterTypRec : (LF.tclo * int -> 'a) -> (LF.head * LF.trec_clo) -> 'a)


(* appendToSpine : LF.spine -> LF.normal -> LF.spine
 *
 * (It would be more efficient to avoid using this function, but it allows a more
 *  direct correspondence between the code and the rules.)
 *)
let rec appendToSpine spine tM = match spine with
        | LF.Nil -> LF.App(tM, LF.Nil)
        | LF.App(tM1, spine) -> LF.App(tM1, appendToSpine spine tM)




(* Rules deriving `App<R>(A > P) |> J':

   App-slashunify
   App-unify
   App-Pi
   App-Sigma *)
let rec app (strategy, shift, cO, cD, cPsi) (tR, spine, tAAA) tP k =
  let _ = dprint (fun () -> "App: tR = " ^ P.headToString cO cD cPsi tR ^ "\n"
                          ^ "App: tA = " ^ P.typToString cO cD cPsi (tAAA, emptySub) ^ "\n"
                          ^ "App: tP = " ^ P.typToString cO cD cPsi (tP, emptySub)) in
  match tAAA with
  | LF.PiTyp (((LF.TypDecl(x, tA1)) as x_decl, _depend), tA2) ->   (* rule App-Pi *)
      let hungPsi = hangDCtx shift cPsi
      and hungtR = hangHead shift tR
      and hungSpine = hangSpine shift spine
      and hungA2 = hangTyp shift tA2
      and hungP = hangTyp shift tP in

      let cPsi_x = LF.DDec(cPsi, x_decl) in
      let _ = dprint (fun () -> "App-Pi: tA = PiTyp(" ^ R.render_name x ^ ":"
                                   ^ P.typToString cO cD cPsi (tA1, emptySub) ^ "), " 
                                   ^ P.typToString cO cD cPsi_x (tA2, emptySub) ^ ")") in
(*      let _ = dprint (fun () -> "App-Pi(0): tA2 = " ^ P.typToString cO cD cPsi_x (tA2, emptySub)) in *)
      let _ = dprint (fun () -> "App-Pi: calling obj to generate instances of "
                        ^ P.typToString cO cD cPsi (tA1, emptySub)) in
      obj (strategy, shift, cO, cD, cPsi) tA1
        (fun (strategy, shift', cO, cD, _cPsi) tM _tA1 ->
           let cPsi = cut hungPsi shift'
           and tR = cut hungtR shift'
           and spine = cut hungSpine shift'
           and tA2 = cut hungA2 shift' (*???*)
           and tP = cut hungP shift' in
           let _ = dprint (fun () -> "App-Pi(tM):   " ^ P.normalToString cO cD cPsi (tM, emptySub)) in
           let _ = dprint (fun () -> "App-Pi(tA2)SH:" ^ P.typToString cO cD cPsi_x (tA2, emptySub)) in
           let substitution = LF.Dot(LF.Obj ((*Context.dctxToHat cPsi,*) tM), emptySub) in
           let tA2_tM = Whnf.normTyp (tA2, substitution) in
           let _ = dprint (fun () -> "App-Pi(1): " ^ P.typToString cO cD cPsi (tA2_tM, emptySub)) in

           let _ = dprint (fun () -> "App-Pi(tR)SH:    " ^ P.headToString cO cD cPsi tR) in

           let _ = dprint (fun () -> "App-Pi(spine)SH: " ^ P.spineToString cO cD cPsi (spine, emptySub)) in

           let _ = dprint (fun () -> "App-Pi(tP)SH:    " ^ P.typToString cO cD cPsi (tP, emptySub)) in
           app (strategy,
                shift' (* we apply the shift to everything here,
                              so we must reset it or we'll overshift  --- NO! *),
                cO,
                cD,
                cPsi)
               (tR,
                appendToSpine spine tM,
                tA2_tM)
                tP
               k)

  | LF.Sigma typ_rec ->     (* rule App-Sigma *)
      begin
        dprint (fun () -> "App-Sigma UNIMPLEMENTED");
        exit 222
      end

  | LF.Atom(loc, a, typeSpine) as tQ ->
      begin
        Debug.indent 2;
        let _ = dprint (fun () -> P.mctxToString cO cD) in
        let msub = mctxToMSub cD in
        let tQ = Whnf.cnormTyp (tQ, msub) in
(*        let tP = Whnf.cnormTyp (tP, msub) in *)
        let unifyLeft = (tQ, emptySub) in 
        let unifyRight = (tP, emptySub) in 
        dprint (fun () -> "App-??unify: " ^ P.typToString cO cD cPsi unifyLeft ^ " =?= "
                             ^ P.typToString cO cD cPsi unifyRight);
        try
            U.unifyTyp cD cPsi unifyLeft unifyRight;
            let cD' = cD in
            let theta_tR = tR in   (* wrong *)
            let theta_tP = tP in   (* wrong *)
            let theta_Psi = cPsi in   (* wrong *)
              k (strategy, shift, cO, cD', theta_Psi) (LF.Root(loc, theta_tR, spine)) (theta_tP);
              Debug.outdent 2
              (* probably wrong: not passing theta along *)          
        with
          U.Unify s ->   (* rule App-slashunify *)
            (dprint (fun () -> "type  " ^ P.typToString cO cD cPsi unifyLeft ^ "  does not unify with  "
                             ^ P.typToString cO cD cPsi unifyRight ^ ";");
             dprint (fun () -> " ignoring  " ^ P.headToString cO cD cPsi tR ^ "  as impossible");
             Debug.outdent 2;
             ()  (* succeed *))
      end



(* obj_split:   Obj-split rule (Fig. 6)
 *)
and obj_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
  let _ = dprint (fun () -> "obj_split: cPsi = " ^ P.dctxToString cO cD cPsi) in
  let _ = dprint (fun () -> "--      a: " ^ R.render_cid_typ a) in
  let _ = dprint (fun () -> "--  spine: " ^ P.spineToString cO cD cPsi (spine, emptySub)) in

  (* PVars premises: *)
  let sch_elems = getParameterSchemaElems cO cPsi in

  (* App<x_1> thru App<x_k> premises: *)
  let concretesWithTypes = getConcretesAndTypes cPsi in

  (* App<c_1> thru App<c_n> premises: *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in

  let callAppOnPVar (LF.SchElem (some_part(*\Theta*), typRec (*\Sigma \Phi. A_{j+1}*) ) as sch_elem) =
    dprint (fun () -> "checking if parameter(s) from schema element  " ^ P.schElemToString sch_elem ^ "  are covered");

    let Some _psi = Context.ctxVar cPsi in

    let some_part_dctx = Context.projectCtxIntoDctx some_part in     
    let some_part_dctxSub = Ctxsub.ctxToSub' cD cPsi some_part_dctx in
(*
    let callOnProjection part 
    let sArec = (LF.SigmaLast nonsigma, emptySub) in


      dprint (fun () -> "sArec  = " ^ P.typRecToString cO cD cPsi sArec
                ^ "\n" ^ "typRec = " ^ P.typRecToString cO cD cPsi (typRec, some_part_dctxSub));
      U.unifyTypRec cD cPsi sArec (typRec, some_part_dctxSub);
*)

      (* let \sigma = --- in *)
      (* let \Delta_\Theta = --- in *)
      let id_psi = Substitution.LF.justCtxVar cPsi in
      let head = LF.PVar (LF.Offset 1, id_psi) in
        match typRec with
          | LF.SigmaLast tA ->
              begin
              let tA = Whnf.normTyp (tA, some_part_dctxSub) in
              let pdecl  = LF.PDecl(new_name "p@", tA, cPsi) in
              let tA = Whnf.mshiftTyp tA 1 in
(*              let cPsi = Whnf.mshiftDCtx cPsi 1 in *)
              let spine = Whnf.mshiftSpine spine 1 in
              let (cDWithPVar, _pdeclOffset) = (LF.Dec(cD, pdecl), 1) in
                dprint (fun () -> "pvar SigmaLast 1\n"
                          ^ "tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                          ^ " P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                if try
                  U.unifyTyp cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub) (tA, emptySub);
                  true
                with U.Unify s ->
                  begin
                    dprnt "callOnComponent unify error; this component impossible";
                    false
                  end
                then begin
                  dprint (fun () -> "pvar SigmaLast 2\n"
                            ^ "tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                            ^ " P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                    dprint (fun () -> "pvar SigmaLast 2\n"
                                          ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                          ^ "--tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                                          ^ "-- P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                    Debug.indent 2;
                    app (decrement_depth strategy, bump_shift 1 shift, cO, cDWithPVar, cPsi)
                      (head, LF.Nil, tA)
                      (LF.Atom(loc, a, spine))
                      k;
                    Debug.outdent 2
                end else ()
              end
          | LF.SigmaElem _ ->
              begin
                let callAppOnComponent (sA, index) =
                  let tA = Whnf.normTyp sA in
                      let typRec = Whnf.normTypRec (typRec, some_part_dctxSub) in
                      let pdecl  = LF.PDecl(new_name "P@", LF.Sigma typRec, cPsi) in
(*                      let tA = Whnf.mshiftTyp tA 1 in*)
                      let spine = Whnf.mshiftSpine spine 1 in
                      let (cDWithPVar, _pdeclOffset) = (LF.Dec(cD, pdecl), 1) in
                    dprint (fun () -> "cPsi(UNSH)= " ^ P.dctxToString cO cDWithPVar cPsi);
(*                      let cPsi = Whnf.mshiftDCtx cPsi 1 in *)
                    dprint (fun () -> "pvar SigmaElem 1 (index = " ^ string_of_int index ^ ")\n"
                                    ^ "cPsi = " ^ P.dctxToString cO cDWithPVar cPsi ^ "\n"
                                    ^ "head = " ^ P.headToString cO cDWithPVar cPsi head ^ "\n"
                                    ^ "sA(UNSHIFTED!!) = " ^ P.typToString cO cDWithPVar cPsi sA ^ "\n"
                                    ^ "tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                                    ^ " P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                    if try
                      U.unifyTyp cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub) (tA, emptySub);
                      true
                    with U.Unify s ->
                      begin
                        dprnt "callOnComponent unify error; this component impossible";
                        false
                      end
                    then begin
                        dprint (fun () -> "pvar SigmaElem 2\n"
                                        ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                        ^ "--tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                                        ^ "-- P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                        Debug.indent 2;
                        app (decrement_depth strategy, bump_shift 1 shift, cO, cDWithPVar, cPsi)
                          (LF.Proj(head, index), LF.Nil, tA)
                          (LF.Atom(loc, a, spine))
                          k;
                        Debug.outdent 2
                    end else ()
                in
                  iterTypRec callAppOnComponent (head, (typRec, some_part_dctxSub    ))
              end

  
  and callAppOnConcrete (LF.BVar x, xTyp) =
        dprint (fun () -> "checking if bound variable \"" ^ R.render_bvar cPsi x ^ "\" is covered");
        Debug.indent 2;
        dprint (fun () -> "--the variable's type is: " ^ P.typToString cO cD cPsi (xTyp, emptySub));
        begin
          match xTyp with
            | LF.Sigma _ -> dprint (fun () -> "--skipping it because it's a block")
            | _ ->
                app (decrement_depth strategy, shift, cO, cD, cPsi)
                    (LF.BVar x, LF.Nil, xTyp)
                    (LF.Atom(loc, a, spine))
                    k
        end;
        Debug.outdent 2

  and callAppOnConstructor (c, cSig) =
        dprint (fun () -> "checking if constructor \"" ^ R.render_cid_term c ^ "\" is covered");
        Debug.indent 2;
        dprint (fun () -> "--type cSig: " ^ P.typToString cO cD cPsi (cSig, emptySub));
        app (decrement_depth strategy, shift, cO, cD, cPsi)
            (LF.Const c, LF.Nil, cSig)
            (LF.Atom(loc, a, spine))
            k;
        Debug.outdent 2
  in
    List.iter callAppOnPVar sch_elems;
    List.iter callAppOnConcrete concretesWithTypes;
    List.iter callAppOnConstructor constructorsWithTypes





(*
 * Obj-no-split / "MVars" rule
 *)
and obj_no_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
  (dprnt "obj_no_split";
   Debug.indent 2;
   let tP = LF.Atom(loc, a, spine) in
   let cPsi1 = cPsi in
   let decl  = LF.MDecl(new_name "NOSPLIT", tP, cPsi1) in
   let tP = Whnf.mshiftTyp tP 1 in
   let (cDWithVar, declOffset) = (LF.Dec(cD, decl), 1) in
   let tR1 : LF.head = LF.MVar(LF.Offset declOffset, Substitution.LF.identity cPsi1)  in
   let tM1 = LF.Root(loc, tR1, LF.Nil) in
   let _ = dprint (fun () -> "obj_no_split:\n"
                           ^ "--cDWithVar = " ^ P.mctxToString cO cDWithVar ^ "\n"
                           ^ "--tM1 (instance) = " ^ P.normalToString cO cDWithVar cPsi1 (tM1, emptySub) ^ "\n"
                           ^ "--tP  = " ^ P.typToString cO cDWithVar cPsi1 (tP, emptySub) ^ "\n"
                           ^ "--tR1 = " ^ P.headToString cO cDWithVar cPsi1 tR1) in
   k (strategy, bump_shift 1 shift, cO, cDWithVar, cPsi1)
     tM1
     tP;
   Debug.outdent 2)



(*
 * Obj-Pi; Obj-Sigma; call to Obj-split/Obj-no-split
 *)
and obj (strategy, shift, cO, cD, cPsi) tA k =
  let _ = dprint (fun () -> "obj: " ^ "\n"
                          ^ "--tA: " ^ P.typToString cO cD cPsi (tA, emptySub)) in
  match tA with
  | LF.PiTyp ((LF.TypDecl(name, tA1) as typdecl, depend), tA2) ->   (* rule Obj-Pi *)
      (dprint (fun () -> "PiTyp");
       Debug.indent 2;
       let hungPsi = hangDCtx shift cPsi in
       let hungA1 = hangTyp shift tA1 in
       let extended_cPsi = LF.DDec(cPsi, typdecl) in
         obj (strategy, shift, cO, cD, extended_cPsi)
             tA2
             (fun (strategy, shift, cO, cD, _extended_cPsi) tM tA2 ->
                let cPsi = cut hungPsi shift in
                let tA1 = cut hungA1 shift in
                let typdecl = LF.TypDecl(name, tA1) in
                k (strategy, shift, cO, cD, cPsi)
                  (LF.Lam(None, name, tM))
                  (LF.PiTyp((typdecl, depend), tA2)));
         Debug.outdent 2)

(*
  | LF.Sigma typ_rec ->  (* rule Obj-Sigma *)
*)
  | LF.Sigma _typ_rec ->
      (dprint (fun () -> "Sigma");
       Debug.indent 2;
       exit 222(*;
       Debug.outdent 2*))

  | LF.Atom (loc, a, spine) ->    (* rule Obj-split *)
     (Debug.indent 2;
      split_switch strategy
         (begin
           (* Split *)
           fun strategy ->  
            obj_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k
          end, begin
           (* Don't split *)
           fun strategy ->
             obj_no_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k
         end);
      Debug.outdent 2)



(*
 * covered_by  BranchBox(cO', cD', (cPsi', tR', msub', csub'), _body) (cO, cD, cPsi) tM tA
 *
 * Succeeds if the term   cD; cPsi |- tM   is covered by   cD'; cPsi' |- tR'
 *)
let covered_by branch (cO, cD, cPsi) tM tA =
  covby_counter := !covby_counter + 1;
  match branch with
  | BranchBox (cO', cD', (cPsi', tR', msub', csub'), _body) ->
      (* under cO / cO' ?
         Pi cD. box(?. tM) : tA[cPsi]  =.  Pi cD'. box(?. tR') : ?[?]   *)
      let _ = dprnt "covered_by" in
      let _ = Debug.indent 2 in

      let _ = dprint (fun () -> "--tR' = "
                              ^ P.normalToString cO' cD' cPsi' (tR', emptySub)) in
      
      let cDConjoint = Context.append cD cD' in
      let _ = dprint (fun () -> "--cDConjoint = "
                              ^ P.mctxToString cO' cDConjoint) in
      let _ = dprint (fun () -> "--cDConjoint = "
                              ^ P.mctxToString cO cDConjoint) in

      let ct = cctxToCSub cO' cD' cPsi' in 
(* let ct' = Ctxsub.ccomp csub' ct in *)
(* let _ = U.unifyCSub csub' ct'  in   (* ......... *) *)
(* let _ct1' = Ctxsub.ctxnorm_csub ct' in *)
      let ct1 = Ctxsub.ctxnorm_csub ct in
      let mt = mctxToMSub (Ctxsub.ctxnorm_mctx (cD', ct1)) in 
      let _ = dprint (fun () -> "**tR' = "
                              ^ P.normalToString cO' cD' cPsi' (tR', emptySub)) in
      let tR' = Whnf.cnorm (Ctxsub.ctxnorm (tR', ct1), mt) in
      let _ = dprint (fun () -> "$$tR' = "
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)) in
(* let _mt1' = Whnf.cnormMSub mt in *)
      let cPsi' = Ctxsub.ctxnorm_dctx (cPsi', ct1) in


      let tM_shifted = Whnf.cnorm (tM, LF.MShift (Context.length cD'))  in

      let _ = dprint (fun () -> P.octxToString cO ^ " |- Pi " ^ P.mctxToString cO cD
                    ^ " box(Psihat. " ^ P.normalToString cO cDConjoint cPsi (tM_shifted, emptySub)
                    ^ ") : " ^ P.typToString cO cD cPsi (tA, emptySub)
                    ^ "["    ^ P.dctxToString cO cD cPsi ^ "]") in
      let _ = dprnt  (" COVERED-BY ") in
      let _ = dprint (fun () -> "$$tR' = "
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)) in
      let _ = dprint (fun () -> P.octxToString cO' ^ " |- Pi " ^ P.mctxToString cO' cD'
                              ^ " box(Psihat. " ^ ""
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)
                              ^ ") : " ^ P.msubToString cO' cD' msub'
                              ^ "[" ^ P.csubToString cO' cD' csub' ^ "]") in
      let matchD = cDConjoint in
      let matchPsi = (****cPsi****) cPsi' in
      let matchLeft = (tM_shifted, emptySub) in
      let matchRight = (tR', emptySub) in
      try
        dprnt ("About to call matchTerm:");
        dprnt ("  matchTerm ");
        dprint (fun () -> "    D = " ^ P.mctxToString cO matchD ^ "\n"
                        ^ "  Psi = " ^ P.dctxToString cO matchD matchPsi ^ "\n"
                        ^ " left = " ^ P.normalToString cO matchD matchPsi matchLeft ^ "\n"
                        ^ "right = " ^ P.normalToString cO matchD matchPsi matchRight);
        U.matchTerm matchD matchPsi matchLeft matchRight;
        dprint (fun () -> "MATCHED");
        Debug.outdent 2
      with U.Unify s -> (dprnt "no match";
                         Debug.outdent 2;
                         raise NoCover)



let rec covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA = match branches with
  | [] -> raise NoCover
  | branch :: branches ->
      try covered_by branch (cO, cD, cPsi) tM tA
      with NoCover -> covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA



let rec maxSpine low f = function
  | LF.Nil -> low
  | LF.App(tM, spine) ->
      let f_tM = f tM in 
        max f_tM (maxSpine f_tM f spine)

let rec maxTuple f = function
  | LF.Last tM -> f tM
  | LF.Cons(tM, tuple) -> max (f tM) (maxTuple f tuple)

and depth = function
  | LF.Lam(_, _, tM) -> 1 + depth tM
  | LF.Root(_, head, spine) -> 1 + (maxSpine (depthHead head) depth spine)
  | LF.Clo(tM, _) -> depth tM
  | LF.Tuple(_, tuple) -> 1 + maxTuple depth tuple

and depthHead = function
  | LF.BVar _ -> 1
  | LF.Const _ -> 1
  | LF.MMVar _ -> 1
  | LF.MVar _ -> 1
  | LF.PVar _ -> 1
  | LF.AnnH (head, _) -> depthHead head
  | LF.Proj (head, _) -> depthHead head

let depth_branch = function
  | BranchBox (_cO', _cD', (_cPsi', tM', _msub', _csub'), _body) ->
      1 + depth tM'

let rec maxDepth branches = match branches with
  | [] -> 0
  | branch :: branches -> max (depth_branch branch) (maxDepth branches)


(* covers : Int.LF.mctx -> Int.LF.mctx -> Int.Comp.ctyp_decl LF.ctx -> Int.Comp.branch list -> (Int.LF.typ * Int.LF.dctx) -> unit
 *
 * covers cO cD cG branches (tA, cPsi)
 *   returns () if the patterns in `branches' cover all values of tA[cPsi];
 *   otherwise, raises NoCover
 *
 * Also returns () if the !enableCoverage flag is false.
 *)
let finish() =
  dprint (fun () -> "covby_counter = " ^ string_of_int !covby_counter);
  Debug.popIndentationLevel()

let covers cO cD cG branches (tA, cPsi) =
  if not (!enableCoverage) then ()
  else
    begin
      covby_counter := 0;
      Debug.pushIndentationLevel();
      Debug.indent 2;
      let cutoff = maxDepth branches in
      let _ = dprint (fun () -> "cutoff depth = " ^ string_of_int cutoff) in
      let strategies = tabulate cutoff naive_strategy in
        try
          dprint (fun () -> "coverage check a case with "
                              ^ string_of_int (List.length branches) ^ " branch(es)");

          tryList
            (fun strategy -> begin
                               Debug.pushIndentationLevel();
                               print_string ("trying strategy " ^ strategyToString strategy ^ "\n"); flush_all();
                               begin try obj (strategy, noop_shift, cO, cD, cPsi)
                                     tA
                                     (covered_by_set branches)
                               with exn -> (Debug.popIndentationLevel(); raise exn)
                               end;
                               Debug.popIndentationLevel()
                             end)
            strategies;

          dprint (fun () -> "## COVERS ##");
          finish()
        with
          NoCover -> (finish(); no_covers := !no_covers + 1; raise NoCover)
    end
