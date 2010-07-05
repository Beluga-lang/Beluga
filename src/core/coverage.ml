(** Coverage checker

   @author Joshua Dunfield
*)

open Syntax.Int
open Syntax.Int.Comp
open ConvSigma

module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module U = Unify.EmptyTrail   (* is EmptyTrail the right one to use?  -jd *)
(*module U = Unify.StdTrail*)
module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [29])

let covby_counter = ref 0

type problem = {loc : Parser.Grammar.Loc.t option;    
                prag : Syntax.case_pragma;           (* indicates if %not appeared after ``case...of'' *)
                cO : LF.mctx;
                cD : LF.mctx;
                branches : Comp.branch list;
                domain : (LF.typ * LF.dctx)}         (* type and context of scrutinee *)

let make loc prag cO cD branches domain =
  {loc= loc;
   prag= prag;
   cO= cO;
   cD= cD;
   branches= branches;
   domain= domain}

type coverage_result =
  | Success
  | Failure of (unit -> string)

exception NoCover of (unit -> string)



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

let shiftHead arg n = Whnf.cnormHead(arg, LF.MShift n)
let shiftSpine arg n = Whnf.cnormSpine(arg, LF.MShift n)
let shiftNormal arg n = Whnf.cnorm(arg, LF.MShift n)
let shiftTyp arg n = Whnf.cnormTyp(arg, LF.MShift n)
let shiftDCtx arg n = Whnf.cnormDCtx(arg, LF.MShift n)

let hangHead = hang Whnf.mshiftHead
let hangSpine = hang Whnf.mshiftSpine
let hangNormal = hang Whnf.mshiftTerm
let hangTyp = hang Whnf.mshiftTyp
let hangDCtx = hang Whnf.mshiftDCtx

let cut (HANGER f) laterShifter = f laterShifter 

let cut = (cut : 'a hanger -> shifter -> 'a)


let bump_shift increment shifter = {n = shifter.n + increment}



(* Coverage is done in 3 phases:
 *
 *   1. ContextDependentArgumentsPhase
 *        possibly split on arguments to dependent types in the context
 *
 *   2. ContextVariablePhase: (NOT YET IMPLEMENTED)
 *        possibly split context variables
 * 
 *   3. TermPhase:
 *        possibly split the object (term)
 *
 *  The LFMTP '08 paper only describes TermPhase.
 *)
type phase =
    ContextDependentArgumentsPhase
  | ContextVariablePhase
  | TermPhase

let phaseToString = function
  | ContextDependentArgumentsPhase -> "ContextDependentArgumentsPhase"
  | ContextVariablePhase -> "ContextVariablePhase"
  | TermPhase -> "TermPhase"
  

(*
 * type strategy  ---Coverage strategy
 *
 * This type represents the strategy---really the *state* and the strategy---being used.
 *)
type strategy = {
  maxDepth : int;
  currDepth : int;
  maxContextLength : int;
  currContextLength : int;
  maxContextDepth : int;
  currContextDepth : int;
  phase : phase
}

let strategyToString s = "{" ^ "maxDepth = " ^ string_of_int s.maxDepth
                             ^ "; currDepth = " ^ string_of_int s.currDepth
                             ^ ";\n                 "
                             ^ "maxContextLength = " ^ string_of_int s.maxContextLength
                             ^ "; currContextLength = " ^ string_of_int s.currContextLength
                             ^ ";\n                 "
                             ^ "maxContextDepth = " ^ string_of_int s.maxContextDepth
                             ^ "; currContextDepth = " ^ string_of_int s.currContextDepth
                             ^ ";\n                 "
                             ^ "phase = " ^ phaseToString s.phase
                             ^ "}"

let naive_strategy (depth, contextLength, contextDepth) =
      {maxDepth = depth;
       currDepth = 0;
       maxContextLength = contextLength;
       currContextLength = 0;
       maxContextDepth = contextDepth;
       currContextDepth = 0;
       phase = ContextDependentArgumentsPhase}

let increment_depth strategy =
(*     print_string ("increment_depth --> " ^ string_of_int (strategy.currDepth + 1) ^ "\n"); flush_all(); *)
      {strategy with currDepth = strategy.currDepth + 1}

let increment_context_length strategy =
      {strategy with currContextLength = strategy.currContextLength + 1}

let increment_context_depth strategy =
      {strategy with currContextDepth = strategy.currContextDepth + 1}


let split_switch strategy (split, noSplit) =
  let couldSplit strategy = strategy.currDepth < strategy.maxDepth in
    if couldSplit strategy then
      begin try   (* Even if the strategy permits us to split, try not splitting, because if it happens
                      to succeed we can save a lot of time *)
         Debug.pushIndentationLevel();
         let result = noSplit strategy in
         Debug.popIndentationLevel();
         result
      with NoCover _ -> (Debug.popIndentationLevel(); split strategy)
      end
    else
      noSplit strategy


let context_split_switch strategy (split, noSplit) =
  let couldSplit strategy = strategy.currContextLength < strategy.maxContextLength in
    if couldSplit strategy && false then
      (try   (* Even if the strategy permits us to split, try not splitting, because if it happens
                  to succeed we can save a lot of time *)
         noSplit strategy
       with NoCover _ -> split strategy)
    else
      noSplit strategy


let contextDep_split_switch strategy (split, noSplit) =
  let couldSplit strategy = strategy.currContextDepth < strategy.maxContextDepth in
    if couldSplit strategy then
      (try   (* Even if the strategy permits us to split, try not splitting, because if it happens
                  to succeed we can save a lot of time *)
         noSplit strategy
       with NoCover _ -> split strategy)
    else
      noSplit strategy


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
  let _ = Types.freeze a in
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
        | [] -> dprnt ""
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


(* getSchemaElems : LF.mctx -> LF.dctx -> LF.sch_elem list
 * getSchemaElems cO cPsi
 *    = [F_1, ..., F_n]   if cPsi has a context variable of schema F_1 + ... + F_n
 *    = []                if cPsi has no context variable
 *)
let getSchemaElems cO cPsi =
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
(*         let _ = dprint (fun () -> "iterTypRec>>> m = " ^ string_of_int m ^ " (len = " ^string_of_int len ^ ")") in *)
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
let rec app (strategy, shift, cO, cD, cPsi) (tR, spine, tA0) tP k =
  let _ = dprint (fun () -> "App: tR = " ^ P.headToString cO cD cPsi tR ^ "\n"
                          ^ "App: tA = " ^ P.typToString cO cD cPsi (tA0, emptySub) ^ "\n"
                          ^ "App: tP = " ^ P.typToString cO cD cPsi (tP, emptySub)) in
  match tA0 with
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
           let _ = dprint (fun () -> "App-Pi(tM):    " ^ P.normalToString cO cD cPsi (tM, emptySub)) in
           let _ = dprint (fun () -> "App-Pi(tA2)SH: " ^ P.typToString cO cD cPsi_x (tA2, emptySub)) in
           let substitution = LF.Dot(LF.Obj ((*Context.dctxToHat cPsi,*) tM), emptySub) in
           let tA2_tM = Whnf.normTyp (tA2, substitution) in
           let _ = dprint (fun () -> "App-Pi(1):     " ^ P.typToString cO cD cPsi (tA2_tM, emptySub)) in
           let _ = dprint (fun () -> "App-Pi(tR):    " ^ P.headToString cO cD cPsi tR) in
           let _ = dprint (fun () -> "App-Pi(spine): " ^ P.spineToString cO cD cPsi (spine, emptySub)) in
           let _ = dprint (fun () -> "App-Pi(tP):    " ^ P.typToString cO cD cPsi (tP, emptySub)) in
           app (strategy,
                shift',
                cO,
                cD,
                cPsi)
               (tR,
                appendToSpine spine tM,
                tA2_tM)
                tP
               k)

  | LF.Sigma typRec ->     (* rule App-Sigma *)
      begin
        let appSigmaComponent (sA, index) =
          let tA = Whnf.normTyp sA in
(*            dprint (fun () -> "cPsi(UNSH)= " ^ P.dctxToString cO cD cPsi); *)
(*                      let cPsi = Whnf.mshiftDCtx cPsi 1 in *)
            dprint (fun () -> "App-Sigma 1 (index = " ^ string_of_int index ^ ")\n"
                            ^ "--cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                            ^ "--  tR = " ^ P.headToString cO cD cPsi tR ^ "\n"
                            ^ "--  sA = " ^ P.typToString cO cD cPsi sA ^ "\n"
                            ^ "--  tA = " ^ P.typToString cO cD cPsi (tA, emptySub) ^ "\n"
                            ^ "--  tP = " ^ P.typToString cO cD cPsi (tP, emptySub));
            if try
              U.unifyTyp cD cPsi (tP, emptySub) (tA, emptySub);
              true
            with U.Unify s ->
              begin
                dprnt "appSigmaComponent unify error; this component impossible";
                false
              end
            then begin
              dprint (fun () -> "App-Sigma 2a\n"
                              ^ "--cD          = " ^ P.mctxToString cO cD ^ "\n"
                              ^ "--tA under cD = " ^ P.typToString cO cD cPsi (tA, emptySub) ^ "\n"
                              ^ "--tP under cD = " ^ P.typToString cO cD cPsi (tP, emptySub));
              app (increment_depth strategy, shift, cO, cD, cPsi)
                  (LF.Proj(tR, index), LF.Nil, tA)
                  tP
                  k;
            end else ()
        in
          iterTypRec appSigmaComponent (tR, (typRec, emptySub))
      end

  | LF.Atom(loc, a, typeSpine) as tQ ->
      begin
        Debug.indent 2;
(*        let _ = dprint (fun () -> "LF.Atom _; cD = " ^ P.mctxToString cO cD) in *)
        let msub = mctxToMSub cD in
        dprint (fun () -> "LF.Atom tQ = " ^ P.typToString cO cD cPsi (tQ, emptySub));
(*        let tQ = Whnf.cnormTyp (tQ, msub) in *)
        let unifyLeft = (tQ, emptySub) in
        let tP_uninst = Whnf.cnormTyp (tP, msub) in
        dprint (fun () -> "LF.Atom tP = " ^ P.typToString cO cD cPsi (tP, emptySub));
        dprint (fun () -> "LF.Atom tP_uninst = " ^ P.typToString cO cD cPsi (tP_uninst, emptySub));
        let unifyRight = (tP_uninst, emptySub) in
        dprint (fun () -> "App-??unify:  " ^ P.typToString cO cD cPsi unifyLeft ^ "  =?=  "
                             ^ P.typToString cO cD cPsi unifyRight);
        try
          U.unifyTyp cD cPsi unifyLeft unifyRight;
          Debug.outdent 2;
          k (strategy, shift, cO, cD, cPsi) (LF.Root(loc, tR, spine)) tP_uninst
        with
          U.Unify s ->   (* rule App-slashunify *)
            (dprint (fun () -> "Type  " ^ P.typToString cO cD cPsi unifyLeft ^ "  does not unify with  "
                             ^ P.typToString cO cD cPsi unifyRight ^ ";");
             dprint (fun () -> " ignoring  " ^ P.headToString cO cD cPsi tR ^ "  as impossible");
             Debug.outdent 2;
             ()  (* succeed *))
      end



(* obj_split:   Obj-split rule (Fig. 6)
 *)
and obj_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
  Debug.indent 4; let k = fun arg1 arg2 arg3 -> (Debug.outdent 4; k arg1 arg2 arg3) in
  dprint (fun () -> "obj_split: cPsi = " ^ P.dctxToString cO cD cPsi);
  dprint (fun () -> "--      a: " ^ R.render_cid_typ a);
  dprint (fun () -> "--  spine: " ^ P.spineToString cO cD cPsi (spine, emptySub));

  (* PVars premises,  App<x_1> thru App<x_k> premises: *)
  let (sch_elems, concretesWithTypes) = match strategy.phase with
                                        | ContextDependentArgumentsPhase -> ([], [])
                                        | ContextVariablePhase -> ([], [])
                                        | TermPhase -> (getSchemaElems cO cPsi, getConcretesAndTypes cPsi)
  in

  (* App<c_1> thru App<c_n> premises: *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in

  let callAppOnPVar (LF.SchElem (some_part(*\Theta*), typRec (*\Sigma \Phi. A_{j+1}*) ) as sch_elem) =
    dprint (fun () -> "checking if parameter(s) from schema element  " ^ P.schElemToString sch_elem ^ "  are covered");

    let Some _psi = Context.ctxVar cPsi in
    
    let some_part_dctx = Context.projectCtxIntoDctx some_part in
    dprint (fun () -> "+++   cD =  " ^ P.mctxToString cO cD ^ "\n"
                    ^ "+++ cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                    ^ "+++ some_part_dctx = " ^ P.dctxToString cO cD some_part_dctx);
    let some_part_dctxSub = Ctxsub.ctxToSub' cD cPsi some_part_dctx in
    dprnt "asdf";
    let id_psi = Substitution.LF.justCtxVar cPsi in
    let head = LF.PVar (LF.Offset 1, id_psi) in
      match typRec with
        | LF.SigmaLast tA ->
            begin
            let tA = Whnf.normTyp (tA, some_part_dctxSub) in
            let name = new_name "p@" in
(*            let _ = dprint (fun () -> "SigmaLast: created parameter \"" ^ R.render_name name ^ "\"") in *)
            let pdecl  = LF.PDecl(name, tA, cPsi) in
            let (cDWithPVar, _pdeclOffset) = (LF.Dec(cD, pdecl), 1) in
              dprint (fun () -> "pvar SigmaLast 1\n"
                        ^ "tA = " ^ P.typToString cO cD cPsi (tA, emptySub) ^ "\n"
                        ^ " P = " ^ P.typToString cO cD cPsi (LF.Atom(loc, a, spine), emptySub));
              if try
                U.unifyTyp cD cPsi (LF.Atom(loc, a, spine), emptySub) (tA, emptySub);
                true
              with U.Unify s ->
                begin
                  dprnt "callOnComponent unify error; this component impossible";
                  false
                end
              then begin
                let tA = shiftTyp tA 1 in
                let spine = shiftSpine spine 1 in
                (*              let cPsi = Whnf.mshiftDCtx cPsi 1 in *)
                 dprint (fun () -> "pvar SigmaLast 2\n"
                                 ^ "--tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                                 ^ "-- P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                  Debug.indent 2;
                  app (increment_depth strategy, bump_shift 1 shift, cO, cDWithPVar, cPsi)
                    (head, LF.Nil, tA)
                    (LF.Atom(loc, a, spine))
                    (fun arg1 arg2 arg3 ->
                       Debug.outdent 2;
                       k arg1 arg2 arg3)
              end else ()
            end
        | LF.SigmaElem _ ->
            begin
              let callAppOnComponent (sA, index) =
                let tA = Whnf.normTyp sA in
                let typRec = Whnf.normTypRec (typRec, some_part_dctxSub) in
                let name = new_name "p@" in
                let _ = dprint (fun () -> "SigmaElem: created parameter \"" ^ R.render_name name ^ "\"") in
                let pdecl  = LF.PDecl(name, LF.Sigma typRec, cPsi) in
                let (cDWithPVar, _pdeclOffset) = (LF.Dec(cD, pdecl), 1) in
                  dprint (fun () -> "pvar SigmaElem 1 (index = " ^ string_of_int index ^ ")\n"
                                  ^ "cPsi = " ^ P.dctxToString cO cDWithPVar (shiftDCtx cPsi 1) ^ "\n"
                                  ^ "head = " ^ P.headToString cO cDWithPVar cPsi head ^ "\n"
                                  ^ "sA(UNSHIFTED) = " ^ P.typToString cO cDWithPVar cPsi sA ^ "\n"
                                  ^ "tA = " ^ P.typToString cO cD cPsi (tA, emptySub) ^ "\n"
                                  ^ " P = " ^ P.typToString cO cD cPsi (LF.Atom(loc, a, spine), emptySub));
                  if try
                    U.unifyTyp cD cPsi (LF.Atom(loc, a, spine), emptySub) (tA, emptySub);
                    true
                  with U.Unify s ->
                    begin
                      dprnt "callOnComponent unify error; this component impossible";
                      false
                    end
                  then begin
                    dprint (fun () -> "pvar SigmaElem 2a\n"
                                      ^ "--cD         = " ^ P.mctxToString cO cD ^ "\n"
                                      ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                      ^ "--tA, unshifted, in cD = " ^ P.typToString cO cD cPsi (tA, emptySub));
                    let cPsi = shiftDCtx cPsi 1 in
                    let tA = shiftTyp tA 1 in
                    let spine = shiftSpine spine 1 in
                      dprint (fun () -> "pvar SigmaElem 2\n"
                                      ^ "--cD         = " ^ P.mctxToString cO cD ^ "\n"
                                      ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                      ^ "--tA = " ^ P.typToString cO cDWithPVar cPsi (tA, emptySub) ^ "\n"
                                      ^ "-- P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), emptySub));
                      Debug.indent 2;
                      app (increment_depth strategy, bump_shift 1 shift, cO, cDWithPVar, cPsi)
                        (LF.Proj(head, index), LF.Nil, tA)
                        (LF.Atom(loc, a, spine))
                        (fun arg1 arg2 arg3 ->
                           Debug.outdent 2;
                           k arg1 arg2 arg3)
                  end else ()
              in
                iterTypRec callAppOnComponent (head, (typRec, some_part_dctxSub))
            end

  
  and callAppOnConcrete (LF.BVar x, xTyp) =
        dprint (fun () -> "checking if bound variable \"" ^ R.render_bvar cPsi x ^ "\" is covered");
        dprint (fun () -> "--the variable's type is: " ^ P.typToString cO cD cPsi (xTyp, emptySub));
        begin
          match xTyp with
            | LF.Sigma _ -> (* dprint (fun () -> "--skipping it because it's a block") *)
                app (increment_depth strategy, shift, cO, cD, cPsi)
                    (LF.BVar x, LF.Nil, xTyp)
                    (LF.Atom(loc, a, spine))
                    k
            | _ ->
                app (increment_depth strategy, shift, cO, cD, cPsi)
                    (LF.BVar x, LF.Nil, xTyp)
                    (LF.Atom(loc, a, spine))
                    k
        end

  and callAppOnConstructor (c, cSig) =
        dprint (fun () -> "checking if constructor \"" ^ R.render_cid_term c ^ "\" is covered");
        dprint (fun () -> "--type cSig: " ^ P.typToString cO cD cPsi (cSig, emptySub));
        app (increment_depth strategy, shift, cO, cD, cPsi)
            (LF.Const c, LF.Nil, cSig)
            (LF.Atom(loc, a, spine))
            k
  in
    List.iter callAppOnPVar sch_elems;
    List.iter callAppOnConcrete concretesWithTypes;
    List.iter callAppOnConstructor constructorsWithTypes





(*
 * Obj-no-split / "MVars" rule
 *)
and obj_no_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
   dprnt "obj_no_split";
   Debug.indent 2;
   let tP = LF.Atom(loc, a, spine) in
   let (flat_cPsi, conv_list) = flattenDCtx cPsi in  
   let s_proj   = gen_conv_sub conv_list in
   let tP' = strans_typ (tP, Substitution.LF.id) conv_list in

   let target_tP = shiftTyp tP 1 in  (* (tP, MShift 1) *)
   dprint (fun () -> "before thin: " ^ P.dctxToString cO cD flat_cPsi);
   let (thin_sub, thin_cPsi) = Subord.thin (cO, cD) (tP', flat_cPsi) in
   (* flat_cPsi |- thin_sub : thin_cPsi *)
   (* flat_cPsi |- tP' type              *)
   let inv_thin_sub = Substitution.LF.invert thin_sub in 
   dprint (fun () -> "s_proj: " ^ P.subToString cO cD cPsi s_proj);
   dprint (fun () -> "thin-subst.: " ^ P.subToString cO cD flat_cPsi thin_sub);
   let decl  = LF.MDecl(new_name "NOSPLIT", LF.TClo(tP', inv_thin_sub), thin_cPsi) in 
   let cDWithVar = LF.Dec(cD, decl) in
   
   let tR1 : LF.head = LF.MVar(LF.Offset 1, Substitution.LF.comp thin_sub s_proj)  in

   (* old code - joshua 
      let cPsi1 = cPsi in 
   let decl  = LF.MDecl(new_name "NOSPLIT", tP, cPsi1) in 
   let tP = shiftTyp tP 1 in
   let (cDWithVar, declOffset) = (LF.Dec(cD, decl), 1) in
(*   let sub = Substitution.LF.identity cPsi1 in *)
   dprint (fun () -> "before thin: " ^ P.dctxToString cO cD cPsi);
   let sub = Subord.thin (cO, cD) (tP, cPsi) in
   dprint (fun () -> "thin-subst.: " ^ P.subToString cO cD cPsi sub);
   let tR1 : LF.head = LF.MVar(LF.Offset declOffset, sub)  in

   let tM1 = LF.Root(loc, tR1, LF.Nil) in
   let _ = dprint (fun () -> "obj_no_split:\n"
                           ^ "--cDWithVar = " ^ P.mctxToString cO cDWithVar ^ "\n"
                           ^ "--tM1 (instance) = " ^ P.normalToString cO cDWithVar cPsi (tM1, emptySub) ^ "\n"
                           ^ "--tP  = " ^ P.typToString cO cDWithVar cPsi (tP, emptySub) ^ "\n"
                           ^ "--tR1 = " ^ P.headToString cO cDWithVar cPsi tR1) in
   *) 
   print_string "*";
   let tM1 = LF.Root(loc, tR1, LF.Nil) in
   dprint (fun () -> "obj_no_split:\n"
                   ^ "--cDWithVar = " ^ P.mctxToString cO cDWithVar);
   dprint (fun () -> "--tM1 (instance) = " ^ P.normalToString cO cDWithVar cPsi (tM1, emptySub));
   dprint (fun () -> "--target_tP = " ^ P.typToString cO cDWithVar cPsi (target_tP, emptySub));
   Debug.outdent 2;
   k (strategy, bump_shift 1 shift, cO, cDWithVar, cPsi (* cPsi1 *))
     tM1
     target_tP  (* tP*)



(*
 * Obj-Pi; Obj-Sigma; call to Obj-split/Obj-no-split
 *)
and obj (strategy, shift, cO, cD, cPsi) tA k =
  dprint (fun () -> "obj: " ^ "\n"
                  ^ "--tA: " ^ P.typToString cO cD cPsi (tA, emptySub));
  match tA with
  | LF.PiTyp ((LF.TypDecl(name, tA1) as typdecl, depend), tA2) ->   (* rule Obj-Pi *)
       dprint (fun () -> "PiTyp");
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
         Debug.outdent 2

  | LF.Sigma _typ_rec ->  (* rule Obj-Sigma *)
       dprint (fun () -> "coverage.ml obj Sigma case...exiting");
       exit 222

  | LF.Atom (loc, a, spine) ->    (* rule Obj-split *)
      split_switch strategy
         (begin
           (* Split *)
           fun strategy ->
             obj_split (strategy, shift, cO, cD, cPsi) (loc, a, spine)
               (fun (strategy', shift, cO, cD, cPsi) b c ->   (* Restore the previous strategy, including strategy.currDepth *)
                  k (strategy, shift, cO, cD, cPsi) b c)
          end, begin
           (* Don't split *)
           fun strategy ->
             obj_no_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k
         end)


let context_split (strategy, shift, cO, cD, cPsi) tA k =
  obj (increment_context_length strategy, shift, cO, cD, cPsi) tA k
(*  let sch_elems = getSchemaElems cO cPsi in
  let splits = ... in
*)


let context (strategy, shift, cO, cD, cPsi) tA k =
   (Debug.indent 2;
    context_split_switch strategy
       (begin
         (* Split *)
         fun strategy -> 
          context_split (strategy, shift, cO, cD, cPsi) tA
            (fun (strategy', shift, cO, cD, cPsi) b c ->   (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, shift, cO, cD, cPsi) b c)
        end, begin
         (* Don't split *)
         fun strategy ->
           dprint (fun () -> "strategy.phase := TermPhase");
           let strategy = {strategy with phase = TermPhase} in
             obj (strategy, shift, cO, cD, cPsi) tA k
       end);
    Debug.outdent 2)


let rec contextDep_split (strategy, shift, cO, cD, cPsi) k =
  let continue (strategy, shift, cO, cD, cPsi) k =
        k (increment_context_depth strategy, shift, cO, cD, cPsi) in
  match cPsi with
    | LF.Null -> continue (strategy, shift, cO, cD, cPsi) k
    | LF.CtxVar _ -> continue (strategy, shift, cO, cD, cPsi) k
    | LF.DDec (cPsi', LF.TypDecl (name, tConcrete)) ->
        begin
          match tConcrete with
            | LF.Atom (loc, a, spine) ->
                let hung_cPsi' = hangDCtx shift cPsi' in
                let a_kind = (Types.get a).Types.kind in

                let rec objSpine (strategy, shift, cO, cD, cPsi') outSpine (inSpine, typ) k =
                  match (inSpine, typ) with
                    | (LF.Nil,  LF.Atom (_loc, _b, _tSpine)) ->
                        k (strategy, shift, cO, cD, cPsi') outSpine
                    | (LF.App(tM, inTail),  LF.PiTyp((LF.TypDecl(_, type_of_tM), _depend), rightTyp)) ->
                          let pass () = objSpine (strategy, shift, cO, cD, cPsi') (LF.App(tM, outSpine)) (inTail, rightTyp) k in
                          let inTail = hangSpine shift inTail in
                          let outSpine = hangSpine shift outSpine in
                          let rightTyp = hangTyp shift rightTyp in
                          begin match tM with
                                | LF.Lam (_loc, _name, _body)    -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.BVar _, _)   -> pass()
                                | LF.Root (_loc, LF.PVar _, _)   -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.Proj _, _)   -> (* impossible? *)   pass()
                                | LF.Root (loc, LF.Const c, innerSpine) ->
                                      objSpine (strategy, shift, cO, cD, cPsi') LF.Nil (innerSpine, (Constructors.get c).Constructors.typ)
                                               (fun (strategy, shift', cO, cD, cPsi') newInnerSpine ->
                                                  let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                                                  let inTail = cut inTail shift' in
                                                  let outSpine = cut outSpine shift' in
                                                  let outSpine = appendToSpine outSpine newRoot in
                                                  let rightTyp = cut rightTyp shift' in
                                                    objSpine (strategy, shift', cO, cD, cPsi') outSpine (inTail, rightTyp) k)
                                | LF.Root (loc, LF.MVar _, _) ->
                                      obj (strategy, shift, cO, cD, cPsi')
                                          type_of_tM
                                          (fun (strategy, shift', cO, cD, _cPsi') splitM _typeOfSplitM ->
                                             let inTail = cut inTail shift' in
                                             let outSpine = cut outSpine shift' in
                                             let outSpine = appendToSpine outSpine splitM in
                                              let rightTyp = cut rightTyp shift' in
                                               objSpine (strategy, shift', cO, cD, cPsi') outSpine (inTail, rightTyp) k)
                          end
                
                and objSpineKind (strategy, shift, cO, cD, cPsi') outSpine (inSpine, kind) k =
                      match (inSpine, kind) with
                      | (LF.Nil,  LF.Typ)  ->  k (strategy, shift, cO, cD, cPsi') outSpine
                      | (LF.App(tM, inTail),  LF.PiKind((LF.TypDecl(_, type_of_tM), _depend), rightKind))  ->
                          let pass () = objSpineKind (strategy, shift, cO, cD, cPsi') (LF.App(tM, outSpine)) (inTail, rightKind) k in
                          let inTail = hangSpine shift inTail in
                          let outSpine = hangSpine shift outSpine in
                          begin match tM with
                                | LF.Lam (_loc, _name, _body)    -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.BVar _, _)   -> pass()
                                | LF.Root (_loc, LF.PVar _, _)   -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible? *)   pass()
                                | LF.Root (_loc, LF.Proj _, _)   -> (* impossible? *)   pass()
                                | LF.Root (loc, LF.Const c, innerSpine) ->
                                      objSpine (strategy, shift, cO, cD, cPsi') LF.Nil (innerSpine, (Constructors.get c).Constructors.typ)
                                               (fun (strategy, shift', cO, cD, cPsi') newInnerSpine ->
                                                  let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                                                  let inTail = cut inTail shift' in
                                                  let outSpine = cut outSpine shift' in
                                                  let outSpine = appendToSpine outSpine newRoot in
                                                    objSpineKind (strategy, shift', cO, cD, cPsi') outSpine (inTail, rightKind) k)

                                | LF.Root (loc, LF.MVar (_, mvarsub), _) ->
                                     (* 1. constrain cPsi' according to mvarsub *)
                                     let cPsi' = LF.Null   (* Substitution.LF.strengthen mvarsub cPsi' *) in
                                     (* 2. thin cPsi' according to typesubordination relation *)
                                        (* ??? *)
                                        obj (strategy, shift, cO, cD, cPsi')
                                            type_of_tM
                                            (fun (strategy, shift', cO, cD, _cPsi') splitM _typeOfSplitM ->
                                               let inTail = cut inTail shift' in
                                               let outSpine = cut outSpine shift' in
                                               let outSpine = appendToSpine outSpine splitM in
                                                 objSpineKind (strategy, shift', cO, cD, cPsi') outSpine (inTail, rightKind) k)
                          end
                in
                  objSpineKind (strategy, shift, cO, cD, cPsi') LF.Nil (spine, a_kind)
                    (fun (strategy, shift', cO, cD, _cPsi') splitSpine ->
                       let cPsi' = cut hung_cPsi' shift' in
                          contextDep (strategy, shift', cO, cD, cPsi')
                             (fun (strategy, shift'', cO, cD, new_cPsi') ->
                                let splitTypDecl = LF.TypDecl (name, LF.Atom (loc, a, splitSpine)) in
                                let reconstitutedPsi = LF.DDec (new_cPsi', splitTypDecl) in
                                  dprint (fun () -> "* splitTypDecl in \"" ^ R.render_name name ^ "\": "
                                                  ^ P.dctxToString cO cD reconstitutedPsi ^ " |- " ^ "___ " ^ P.spineToString cO cD reconstitutedPsi (splitSpine, emptySub));
                                  continue (strategy, shift'', cO, cD, reconstitutedPsi) k))

            | whatever ->
                let tConcrete = hangTyp shift tConcrete in
                 contextDep (strategy, shift, cO, cD, cPsi')
                   (fun (strategy, shift', cO, cD, new_cPsi') ->
                      let tConcrete = cut tConcrete shift' in
                        continue (strategy, shift', cO, cD, LF.DDec (new_cPsi', LF.TypDecl (name, tConcrete))) k)
        end



and contextDep (strategy, shift, cO, cD, cPsi) k =
(*           k (strategy, shift, cO, cD, cPsi) *)
    Debug.indent 2;
    contextDep_split_switch strategy
       (begin
         (* Split *)
         fun strategy -> 
          contextDep_split (strategy, shift, cO, cD, cPsi)
            (fun (strategy', shift, cO, cD, cPsi) ->
               Debug.outdent 2;
               (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, shift, cO, cD, cPsi))
        end, begin
         (* Don't split *)
         fun strategy ->
           Debug.outdent 2;
           k (strategy, shift, cO, cD, cPsi)
       end)



(*
 * covered_by  BranchBox(cO', cD', (cPsi', tR', msub', csub'), _body) (cO, cD, cPsi) tM tA
 *
 * Succeeds iff the term   cD; cPsi |- tM   is covered by   cD'; cPsi' |- tR'
 *)
let covered_by branch (cO, cD, cPsi) tM tA =
  covby_counter := !covby_counter + 1;
  match branch with
  | BranchBox (cO', cD', (cPsi', tR', msub', csub'), _body) ->
      (* under cO / cO' ?
         Pi cD. box(?. tM) : tA[cPsi]  =.  Pi cD'. box(?. tR') : ?[?]   *)
      dprnt "covered_by";
      Debug.indent 2;
      dprint (fun () -> "--cPsi' = " ^ P.dctxToString cO' cD' cPsi' ^ "\n"
                      ^ "--  tR' = " ^ P.normalToString cO' cD' cPsi' (tR', emptySub) ^ "\n"
                      ^ "--msub' = " ^ P.msubToString cO' cD' msub' ^ "\n"
                      ^ "--csub' = " ^ P.csubToString cO' cD' csub');
      
      let cDConjoint = Context.append cD cD' in
      dprint (fun () -> "--cDConjoint = " ^ P.mctxToString cO cDConjoint ^ "\n"
                     ^  "--cPsi  = " ^ P.dctxToString cO cD cPsi ^ "\n"
                     ^ "--cPsi' = " ^ P.dctxToString cO cDConjoint cPsi');
      
      let ct = cctxToCSub cO' cD' cPsi' in
(* let ct' = Ctxsub.ccomp csub' ct in (* AAA *) *)
(* let _ct1' = Ctxsub.ctxnorm_csub ct' in *)
      let ct1 = Ctxsub.ctxnorm_csub ct in
      let mt = mctxToMSub (Ctxsub.ctxnorm_mctx (cD', ct1)) in
      let tR' = Whnf.cnorm (Ctxsub.ctxnorm (tR', ct1), mt) in
(*      let _ = dprint (fun () -> "--tR' in cDConjoint = "
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)) in *)
(* let _mt1' = Whnf.cnormMSub mt in *)
      let cPsi' = Ctxsub.ctxnorm_dctx (cPsi', ct1) in
      
      let shift_unprimed = LF.MShift (Context.length cD') in
      let tM_shifted = Whnf.cnorm (tM, shift_unprimed)  in
      
      let _ = dprint (fun () -> P.octxToString cO ^ " |- Pi " ^ P.mctxToString cO cD
                    ^ " box(Psihat. " ^ P.normalToString cO cDConjoint cPsi (tM_shifted, emptySub)
                    ^ ") : " ^ P.typToString cO cD cPsi (tA, emptySub)
                    ^ "["    ^ P.dctxToString cO cD cPsi ^ "]") in
      let _ = dprnt  (" COVERED-BY ") in
      let _ = dprint (fun () -> P.octxToString cO' ^ " |- Pi " ^ P.mctxToString cO' cD'
                              ^ " box(" ^ P.dctxToString cO' cD' cPsi' ^ " . " ^ ""
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)
                              ^ ") : " ^ P.msubToString cO' cD' msub'
                              ^ "[" ^ P.csubToString cO' cD' csub' ^ "]") in
      let matchD = cDConjoint in
      let matchPsi = cPsi' in
      let matchLeft = (tM_shifted, emptySub) in
      let matchRight = (tR', emptySub) in
      
      let cPsi' = Whnf.cnormDCtx (cPsi', mt) in

      let cPsi = Whnf.cnormDCtx (cPsi, shift_unprimed) in
      try
        dprint (fun () -> " cPsi  = " ^ P.dctxToString cO cDConjoint cPsi ^ "\n"
                        ^ " cPsi' = " ^ P.dctxToString cO cDConjoint cPsi');

        U.unifyDCtx cO' cDConjoint cPsi cPsi';
        
        dprnt ("About to call:\n  matchTerm ");
        dprint (fun () -> "    D = " ^ P.mctxToString cO matchD ^ "\n"
                        ^ "  Psi = " ^ P.dctxToString cO matchD matchPsi ^ "\n"
                        ^ " left = " ^ P.normalToString cO matchD matchPsi matchLeft ^ "\n"
                        ^ "right = " ^ P.normalToString cO matchD matchPsi matchRight);

        U.matchTerm matchD matchPsi matchLeft matchRight;

        dprint (fun () -> "MATCHED");
        Debug.outdent 2
      with U.Unify s -> (dprnt "no match";
                         Debug.outdent 2;
                         raise (NoCover (fun () -> "---inner NoCover escaped---")))



let rec covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA = match branches with
  | [] -> raise (NoCover (fun () -> "Not covered: "
                                  ^ "[" ^ P.dctxToString cO cD cPsi ^ "]  "
                                  ^ P.normalToString cO cD cPsi (tM, emptySub)))
  | branch :: branches ->
      try covered_by branch (cO, cD, cPsi) tM tA;
        dprint (fun () -> "Term covered:  " ^ P.normalToString cO cD cPsi (tM, emptySub)
                  ^ "  covered by  "
                  ^ (match branch with BranchBox (cO', cD', (cPsi', tR', _msub', _csub'), _body) ->
                          P.normalToString cO' cD' cPsi' (tR', emptySub)))
      with NoCover _ -> covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA


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
  | LF.MVar _ -> 0
  | LF.PVar _ -> 1
  | LF.AnnH (head, _) -> depthHead head
  | LF.Proj (head, _) -> depthHead head

let rec maxfun f = function
  | [] -> 0
  | x :: xs -> let f_x = f x in max f_x (maxfun f xs)



let rec maxTypRec f = function
  | LF.SigmaLast tA -> f tA
  | LF.SigmaElem(_x, tA, typRec) ->
      max (f tA) (maxTypRec f typRec)


let rec dependentDepth = function
  | LF.Atom(_loc, _a, spine) -> maxSpine 1 depth spine
  | LF.PiTyp ((typdecl, _depend), tA) ->
      1 + dependentDepth tA
  | LF.Sigma typ_rec -> 1 + maxTypRec dependentDepth typ_rec

let rec dependentDepth_dctx = function
  | LF.Null -> 0
  | LF.CtxVar _ -> 0
  | LF.DDec (cPsi, LF.TypDecl(_name, tA)) ->
      let dd_tA = dependentDepth tA - 1 in
      (dprint (fun () -> "dependentDepth_dctx " ^ string_of_int dd_tA);
       max (dd_tA) (dependentDepth_dctx cPsi))


(* Lifted to branch *)

let depth_branch = function
  | BranchBox (_cO', _cD', (_cPsi', tM', _msub', _csub'), _body) ->
      1 + depth tM'

let length_branch = function
  | BranchBox (_cO', _cD', (cPsi', _tM', _msub', _csub'), _body) ->
      Context.dctxLength cPsi'

let dependentDepth_branch = function
  | BranchBox (_cO', _cD', (cPsi', _tM', _msub', _csub'), _body) ->
      dependentDepth_dctx cPsi'

(* Lifted to (branch list) *)
let maxDepth branches = maxfun depth_branch branches
let maxContextLength branches = maxfun length_branch branches
let maxDependentDepth branches = maxfun dependentDepth_branch branches


(* covers : Int.LF.mctx -> Int.LF.mctx -> Int.Comp.ctyp_decl LF.ctx -> Int.Comp.branch list -> (Int.LF.typ * Int.LF.dctx) -> unit
 *
 * covers cO cD cG branches (tA, cPsi)
 *   returns Success if the patterns in `branches' cover all values of tA[cPsi];
 *   otherwise, returns Failure messageFn where messageFn() is an appropriate error message.
 *
 * Also returns Success if the !enableCoverage flag is false.
 *)
let finish() =
  dprint (fun () -> "covby_counter = " ^ string_of_int !covby_counter);
  Debug.popIndentationLevel()

let covers problem =
  if not (!enableCoverage) then Success
  else
    let (tA, cPsi) = problem.domain in
      covby_counter := 0;
      Debug.pushIndentationLevel();
      Debug.indent 2;
      let cutoff = maxDepth problem.branches
      and length = maxContextLength problem.branches
      and dep = maxDependentDepth problem.branches
      in
      let _ = dprint (fun () -> "cutoff depth        = " ^ string_of_int cutoff) in
      let _ = dprint (fun () -> "max context length  = " ^ string_of_int length) in
      let _ = dprint (fun () -> "max dependent depth = " ^ string_of_int dep) in
      let strategies = tabulate cutoff (fun depth -> naive_strategy (depth, length, dep)) in
        try
          dprint (fun () -> "Coverage checking a case with "
                              ^ string_of_int (List.length problem.branches) ^ " branch(es)");
          tryList
            (fun strategy ->
               Debug.pushIndentationLevel();
               print_string ((fun () -> "trying strategy " ^ strategyToString strategy)() ^ "\n");
               begin try
                           let shift = noop_shift in
                           let tA = hangTyp shift tA in
                             contextDep (strategy, shift, problem.cO, problem.cD, cPsi)
                               (fun (strategy, shift', cO, cD, cPsi) ->
                                  dprint (fun () -> "contextDep generated cPsi = " ^ P.dctxToString cO cD cPsi);
                                  dprint (fun () -> "strategy.phase := ContextVariablePhase");
                                  let strategy = {strategy with phase = ContextVariablePhase} in
                                  let tA = cut tA shift' in
                                    context (strategy, shift', cO, cD, cPsi)
                                            tA
                                            (covered_by_set problem.branches))
               with exn -> (Debug.popIndentationLevel(); raise exn)
               end;
               Debug.popIndentationLevel())
            strategies;

          dprint (fun () -> "## COVERS ##");
          finish();
          begin match problem.prag with
                | Syntax.RegularCase -> Success
                | Syntax.PragmaNotCase ->
                    Failure (fun () ->
                               Printf.sprintf "\n## Case expression covers, UNSOUNDLY(?): ##\n##   %s\n##\n\n"
                                        (Pretty.locOptToString problem.loc))
          end
        with
          NoCover messageFn ->
            begin
              finish();
              no_covers := !no_covers + 1;
              match problem.prag with
                | Syntax.RegularCase ->
                    Failure (fun () ->
                               Printf.sprintf "\n## Case expression doesn't cover: ##\n##   %s\n##   %s\n\n"
                                              (Pretty.locOptToString problem.loc)
                                              (messageFn()))
                | Syntax.PragmaNotCase ->
                   (Printf.printf "\n## Case expression doesn't cover, consistent with \"case ... of %%not\" ##\n##   %s\n##   %s\n\n"
                                  (Pretty.locOptToString problem.loc)
                                  (messageFn());
                    Success)
            end


let process problem =
  match covers problem with
  | Success -> ()
  | Failure messageFn ->
      if !warningOnly then
        Error.addInformation ("WARNING: Cases didn't cover: " ^ messageFn())
      else
        raise (NoCover messageFn)


let problems = ref ([] : problem list)

let clear () =
  problems := []

let stage problem =
  problems := problem::!problems

let force f =
  List.map (fun problem -> f (covers problem)) (List.rev !problems)
