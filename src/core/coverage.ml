(** Coverage checker

   @author Joshua Dunfield
*)

open Syntax.Int
open Syntax.Int.Comp
open ConvSigma

module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module U = Unify.EmptyTrail
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
             failwith "tryList")


let cctxToCSub = Opsem.cctxToCSub
let mctxToMSub = Ctxsub.mctxToMSub


(* type shifter
 *
 * Shifter passed into the continuation, to fix indices in things created
 * before Delta was extended.
 *
 * shifter.n = (length of the "current" cD)
 *           - (length of the original cD passed to the coverage checker)
 *
 * This field `n' is not accessed except inside shift*, hang*, and bump_shift.
 * 
 * To use a shifter, one "hangs" (suspends) a shiftable object (head, spine, normal, LF.typ, or dctx)
 * along with the current shifter, by calling hangHead, hangSpine, etc.  The result has
 * type 'a hanger, where 'a is head, spine, etc.
 *
 * Inside a passed continuation (or in any other situation where cD may have grown unpredictably),
 * the hanger can be "cut" (forced) to yield a properly shifted object that makes sense in the new cD.
 *
 * In most of the coverage checker, the hanger let-binding shadows the unshifted object's
 * binding, so that ocaml gives a type error if you try to use the object without
 * shifting it properly.
 *)
type shifter = {
  n : int
}

type 'a hanger = HANGER of (shifter -> 'a)


let noop_shift = {
  n = 0
}

let hang shiftFn shifter thing =
  HANGER (fun laterShifter -> shiftFn thing (laterShifter.n - shifter.n))
let hang = (hang : ('a -> int -> 'a) -> shifter -> 'a -> 'a hanger)

let shiftHead head n = Whnf.cnormHead(head, LF.MShift n)
let shiftSpine spine n = Whnf.cnormSpine(spine, LF.MShift n)
let shiftNormal tM n = Whnf.cnorm(tM, LF.MShift n)
let shiftTyp typ n = Whnf.cnormTyp(typ, LF.MShift n)
let shiftDCtx cPsi n = Whnf.cnormDCtx(cPsi, LF.MShift n)

let sHead head msub =
  let root = LF.Root(None, head, LF.Nil) in
    match Whnf.cnorm (root, msub) with
      | LF.Root(_, head, LF.Nil) -> head
      | _ -> (print_string "broken (coverage.ml)\n"; exit 88)
        
let sSpine spine msub = Whnf.cnormSpine (spine, msub)
let sNormal tM msub = Whnf.cnorm (tM, msub)
let sTyp tA msub = Whnf.cnormTyp (tA, msub)
let sDCtx cPsi msub = Whnf.cnormDCtx (cPsi, msub)


let hangHead = hang Whnf.mshiftHead
let hangSpine = hang Whnf.mshiftSpine
let hangNormal = hang Whnf.mshiftTerm
let hangTyp = hang Whnf.mshiftTyp
let hangDCtx = hang Whnf.mshiftDCtx

let cut (HANGER f) laterShifter = f laterShifter 

let cut = (cut : 'a hanger -> shifter -> 'a)


let bump_shift increment shifter = {n = shifter.n + increment}


let original_cD_length = ref (-999)
let original_cD = ref LF.Empty


(* Invariants of the 5-tuple (strategy, ms, cO, cD, cPsi):
   
    cO |- cD mctx                      [not checked by verify]
    cO; cD |- cPsi dctx                [checked]
*)

(*
          let verify (shift, cO, cD, cPsi) =
            (* 1. Verify shift with respect to cD *)
            (if !original_cD_length + shift.n = Context.length cD then
              ()
            else
              (print_string "verify failed -- shift not consistent with length of cD\n"; exit 55));
            (* 2. Verify cO; cD |- cPsi well-formed dctx *)
            (dprint (fun () -> "checkDCtx cO;\n"
                             ^ "   cD = " ^ P.mctxToString cO cD ^ "\n"
                             ^ " cPsi = " ^ P.dctxToString cO cD cPsi);
             Lfcheck.checkDCtx cO cD cPsi)
*)

let verify (ms, cO, cD, cPsi) =
(* NO --- WRONG
  (* 1. Verify cO; cD |- ms : original_cD *)
  dprint (fun () -> "checkMSub cO;\n"
                  ^ "   cD = " ^ P.mctxToString cO cD ^ "\n"
                  ^ "   ms = " ^ P.dctxToString cO cD cPsi ^ "\n"
                  ^ "   original_cD = " ^ P.mctxToString cO !original_cD);
  Lfcheck.checkMSub cO cD ms !original_cD;
*)
  (* 2. Verify cO; cD |- cPsi well-formed dctx *)
  dprint (fun () -> "checkDCtx cO;\n"
                  ^ "   cD = " ^ P.mctxToString cO cD ^ "\n"
                  ^ " cPsi = " ^ P.dctxToString cO cD cPsi);
  Lfcheck.checkDCtx cO cD cPsi



(* Coverage has 3 phases:
 *
 *   1. ContextVariablePhase:
 *        possibly split context variables
 * 
 *   2. ContextDependentArgumentsPhase
 *        possibly split on arguments to dependent types in the context
 *
 *   3. TermPhase:
 *        possibly split the object (term)
 *
 *  The LFMTP '08 paper only describes TermPhase.
 *)
type phase =
  | ContextVariablePhase
  | ContextDependentArgumentsPhase
  | TermPhase

let phaseToString = function
  | ContextVariablePhase -> "ContextVariablePhase"
  | ContextDependentArgumentsPhase -> "ContextDependentArgumentsPhase"
  | TermPhase -> "TermPhase"
  

(*
 * type strategy  ---Coverage strategy
 *
 * This type represents the strategy---really the *state* and the strategy---being used.
 *)
type strategy = {
  phase : phase;
  maxDepth : int;
  currDepth : int;
  maxContextVariableDepth : int;
  currContextVariableDepth : int;
  maxContextDepth : int;
  currContextDepth : int
}

let strategyToString s = "{" ^ "maxDepth = " ^ string_of_int s.maxDepth
                             ^ "; currDepth = " ^ string_of_int s.currDepth
                             ^ ";\n                 "
                             ^ "maxContextVariableDepth = " ^ string_of_int s.maxContextVariableDepth
                             ^ "; currContextVariableDepth = " ^ string_of_int s.currContextVariableDepth
                             ^ ";\n                 "
                             ^ "maxContextDepth = " ^ string_of_int s.maxContextDepth
                             ^ "; currContextDepth = " ^ string_of_int s.currContextDepth
                             ^ ";\n                 "
                             ^ "phase = " ^ phaseToString s.phase
                             ^ "}"

let naive_strategy (depth, contextVariableDepth, contextDepth) =
      {maxDepth = depth;
       currDepth = 0;
       maxContextVariableDepth = contextVariableDepth;
       currContextVariableDepth = 0;
       maxContextDepth = contextDepth;
       currContextDepth = 0;
       phase = ContextVariablePhase}

let increment_context_variable_depth strategy =
      {strategy with currContextVariableDepth = strategy.currContextVariableDepth + 1}

let increment_context_depth strategy =
      {strategy with currContextDepth = strategy.currContextDepth + 1}

let increment_depth strategy =
(*     print_string ("increment_depth --> " ^ string_of_int (strategy.currDepth + 1) ^ "\n"); flush_all(); *)
      {strategy with currDepth = strategy.currDepth + 1}



(* context_split_switch,
 * contextDep_split_switch,
 * split_switch
 * : strategy -> ((strategy -> 'a) * (strategy -> 'a)) -> 'a
 *
 * Given a strategy and a pair of functions (split, noSplit),
 *  check whether the current depth is less than the maximum depth.
 * If so, try noSplit (because not splitting is faster than splitting);
 *  if NoCover is raised, call split.
 * If we have reached the maximum depth, call noSplit.
 *
 * The "current depth" and "maximum depth" above vary:
 *
 *  context_split_switch     uses  strategy.{curr,max}ContextVariableDepth
 *  contextDep_split_switch  uses  strategy.{curr,max}ContextDepth
 *  split_switch             uses  strategy.{curr,max}Depth
 *
 * NOTE: these functions do not increment the depth.
 *)
let context_split_switch strategy (split, noSplit) =
  let couldSplit strategy = strategy.currContextVariableDepth < strategy.maxContextVariableDepth in
    if couldSplit strategy then
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



(* Flags
 *)
let enableCoverage = ref false  (* true iff coverage should be checked *)
let warningOnly = ref false     (* true iff failed coverage should generate a warning *)
let extraDepth = ref 0          (* amount of split depth, in addition to the supposedly adequate amount *)
let no_covers = ref 0           (* number of times coverage checking has yielded a negative result *)


(* Generating meta-variable and parameter variable names,
 *  e.g. for Obj-no-split (MVars)
 *)
let counter = ref 0

let new_parameter_name string =
   counter := !counter + 1;
   Id.mk_name (Id.SomeString (string ^ string_of_int !counter))

let new_name string =
   new_parameter_name (String.uppercase string)



let idSub = Substitution.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)
let idMSub = Whnf.m_id


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
                   ^ " : " ^ P.typToString cO cD cPsi (cSig, idSub));
              dprintCTs cO cD cPsi rest)


(* getConcretesAndTypes : LF.dctx -> (LF.head * LF.typ) list
 *
   getConcretesAndTypes cPsi = L 

   for each x:tA in cPsi,   (x, tA) is in L  and  cPsi |- tA : type

 *)
let getConcretesAndTypes cPsi =
  let rec inner n s = function
  (* where   cPsi |- s : cPsi' *)
    | LF.Null -> []
    | LF.CtxVar _ -> []
    | LF.DDec (cPsi', LF.TypDecl(x, tA)) ->
        (* cPsi |- s : cPsi', x:tA  *)
        let s' = Substitution.LF.comp (Substitution.LF.shift) s in
	(* cPsi |- s' : cPsi' *)
        let tA = Whnf.normTyp (tA, s') in
          (LF.BVar n, tA) :: inner (n+1) s' cPsi'
  in
    List.rev (inner 1 Substitution.LF.id cPsi)


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
 

(* iterTypRec f (head, s_recA) = ()
 
   if   cO ; cD ; cPsi |- s_recA : type
          f: tclo * int ->  unit
   then
      for 1 <= m <= block-length(s_recA),
        call f (sA, m)  where  cO ; cD ; cPsi |- sA : type
                          and  sA is the mth component of the block s_recA.
*)
let rec iterTypRec f (head, s_recA) =
  let typRec = Whnf.normTypRec s_recA in
(*  let _ = dprint (fun () -> "iterTypRec>>> " ^ string_of_int (lenTypRec typRec)) in *)
  let len = lenTypRec typRec in
    range
      len
      (fun m ->
         let m = len - m in  (* range counts down, but it's more intuitive to start from 0 *)
         let sA = LF.getType head (typRec, idSub) m 1 in
           dprint (fun () -> "iterTypRec>>> m = " ^ string_of_int m ^ " (len = " ^string_of_int len ^ ")");
           f (sA, m))

let iterTypRec = (iterTypRec : (LF.tclo * int -> unit) -> (LF.head * LF.trec_clo) -> unit)


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
(* 
   cO ; cD ; cG |-   Pi cD_i . pat -> body  <=_{P[Psi]}  tau
   tR = head
   cO ; cD ; cPsi |- tR spine : tA0
   k is the continuation J
*)
let rec app (strategy, (ms : LF.msub), cO, cD, cPsi) (tR, spine, tA0) tP k =
  let _ = dprint (fun () -> "App: tR  = " ^ P.headToString cO cD cPsi tR ^ "\n"
                          ^ "App: tA0 = " ^ P.typToString cO cD cPsi (tA0, idSub) ^ "\n"
                          ^ "App: tP  = " ^ P.typToString cO cD cPsi (tP, idSub)) in
(*  verify (shift, cO, cD, cPsi); *)
  Lfcheck.checkTyp cO cD cPsi (tA0, idSub);
  dprnt "checkTyp tA0 OK";
  Lfcheck.checkTyp cO cD cPsi (tP, idSub);
  dprnt "checkTyp tP OK";
(*  always fails because not eta-expanded
   Lfcheck.check cO cD cPsi (LF.Root(None, tR, spine), idSub) (tA0, idSub);
  dprnt "check OK";
*)
  match tA0 with
  | LF.PiTyp (((LF.TypDecl(x, tA1)) as x_decl, _depend), tA2) ->   (* rule App-Pi *)
(*      let hungPsi = hangDCtx shift cPsi
      and hungtR = hangHead shift tR
      and hungSpine = hangSpine shift spine
      and hungA2 = hangTyp shift tA2
      and hungP = hangTyp shift tP in
*)
      let cPsi_x = LF.DDec(cPsi, x_decl) in
      let _ = dprint (fun () -> "App-Pi: tA = PiTyp(" ^ R.render_name x ^ ":"
                                   ^ P.typToString cO cD cPsi (tA1, idSub) ^ "), \n                    "
                                   ^ P.typToString cO cD cPsi_x (tA2, idSub) ^ ")") in
(*      let _ = dprint (fun () -> "App-Pi(0): tA2 = " ^ P.typToString cO cD cPsi_x (tA2, idSub)) in *)
      let _ = dprint (fun () -> "App-Pi: calling obj to generate instances of "
                        ^ P.typToString cO cD cPsi (tA1, idSub)) in
      obj (strategy, idMSub, cO, cD, cPsi) tA1
        (fun (strategy, ms', cO, cD, cPsi) tM _tA1 ->
(*           let ms = Substitution.LF.comp ms' ms in *)
           let tR = sHead tR ms' in
           let spine = sSpine spine ms' in
           let tA2 = sTyp tA2 ms' in
           let tP = sTyp tP ms' in
           let _ = dprint (fun () -> "App-Pi(tM):    " ^ P.normalToString cO cD cPsi (tM, idSub)) in
(*           let _ = dprint (fun () -> "App-Pi(tA2)SH: " ^ P.typToString cO cD cPsi_x (tA2, idSub)) in *)
           let substitution = LF.Dot(LF.Obj tM, (*Substitution.LF.identity cPsi*)idSub) in
           let _ = dprint (fun () -> "substitution:  " ^ P.subToString cO cD cPsi substitution) in
           let tA2_tM = Whnf.normTyp (tA2, substitution) in

           let _ = dprint (fun () -> "App-Pi(1):     " ^ P.typToString cO cD cPsi (tA2_tM, idSub)) in
           let _ = Lfcheck.checkTyp cO cD cPsi (tA2_tM, idSub) in 
           let _ = dprint (fun () -> "App-Pi(tR):    " ^ P.headToString cO cD cPsi tR) in
           let _ = dprint (fun () -> "App-Pi(spine): " ^ P.spineToString cO cD cPsi (spine, idSub)) in
           let _ = dprint (fun () -> "App-Pi(tP):    " ^ P.typToString cO cD cPsi (tP, idSub)) in
           app (strategy,
                Whnf.mcomp ms ms',
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
        (* cO ; cD ; cPsi |- sA : type *)
        let appSigmaComponent (sA, index) =
          let tA = Whnf.normTyp sA in
(*            dprint (fun () -> "cPsi(UNSH)= " ^ P.dctxToString cO cD cPsi); *)
(*                      let cPsi = Whnf.mshiftDCtx cPsi 1 in *)
            dprint (fun () -> "App-Sigma 1 (index = " ^ string_of_int index ^ ")\n"
                            ^ "--cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                            ^ "--  tR = " ^ P.headToString cO cD cPsi tR ^ "\n"
                            ^ "--  sA = " ^ P.typToString cO cD cPsi sA ^ "\n"
                            ^ "--  tA = " ^ P.typToString cO cD cPsi (tA, idSub) ^ "\n"
                            ^ "--  tP = " ^ P.typToString cO cD cPsi (tP, idSub));
            if try
              (* XXX broken *)
              U.unifyTyp cD cPsi (tP, idSub) (tA, idSub);
              true
            with U.Unify s ->
              begin
                dprnt "appSigmaComponent unify error; this component impossible";
                false
              end
            then begin
              dprint (fun () -> "App-Sigma 2a\n"
                              ^ "--cD          = " ^ P.mctxToString cO cD ^ "\n"
                              ^ "--tA under cD = " ^ P.typToString cO cD cPsi (tA, idSub) ^ "\n"
                              ^ "--tP under cD = " ^ P.typToString cO cD cPsi (tP, idSub));
              app (increment_depth strategy, ms, cO, cD, cPsi) (* do we need to increment depth here? *)
                  (LF.Proj(tR, index), LF.Nil, tA)
                  tP
                  k;
            end else ()
        in
          iterTypRec appSigmaComponent (tR, (typRec, idSub))
      end

  | LF.Atom(loc, a, typeSpine) as tQ ->
      begin
        dprnt "Entering LF.Atom case of app";
        Debug.indent 2;
        dprint (fun () -> "tA0=tQ atomic; \n    cD = " ^ P.mctxToString cO cD
                        ^ "\n  cPsi = " ^ P.dctxToString cO cD cPsi
                        ^ "\n  TERM = " ^ P.normalToString cO cD cPsi (LF.Root(None, tR, spine), idSub)
                        ^ "\n   tA0 = " ^ P.typToString cO cD cPsi (tA0, idSub)
                        ^ "\n   tP  = " ^ P.typToString cO cD cPsi (tP, idSub));
        Lfcheck.check cO cD cPsi (LF.Root(None, tR, spine), idSub) (tA0, idSub);   (* used to break for test/cd2.bel*)
        dprnt "Lfcheck.check against tA0 (a.k.a. tQ) OK";
(*        let _ = dprint (fun () -> "LF.Atom _; cD = " ^ P.mctxToString cO cD) in *)
        let abstractor_msub = mctxToMSub cD in
        dprint (fun () -> "LF.Atom tQ = " ^ P.typToString cO cD cPsi (tQ, idSub));
        let unifyLeft =  (Whnf.cnormTyp (tQ, abstractor_msub), idSub) in
        let tP_uninst = Whnf.cnormTyp (tP, abstractor_msub) in
        dprint (fun () -> "LF.Atom tP = " ^ P.typToString cO cD cPsi (tP, idSub));
        dprint (fun () -> "LF.Atom tP_uninst = " ^ P.typToString cO cD cPsi (tP_uninst, idSub));
        let unifyRight = (tP_uninst, idSub) in
        dprint (fun () -> "App-??unify:  " ^ P.typToString cO cD cPsi unifyLeft ^ "  =?=  "
                             ^ P.typToString cO cD cPsi unifyRight);
        try
          U.unifyTyp LF.Empty cPsi unifyLeft unifyRight;
          Debug.outdent 2;
          let (theta, cDAbstracted) = Abstract.abstractMSub abstractor_msub in
          let cD = cDAbstracted in
          let cPsi = sDCtx cPsi theta in
          let tR = sHead tR theta in
          let spine = sSpine spine theta in
            k (strategy, Whnf.mcomp ms theta, cO, cD, cPsi) (LF.Root(loc, tR, spine)) tP_uninst
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
and obj_split (strategy, (ms : LF.msub), cO, cD, cPsi) (loc, a, spine) k =
  Debug.indent 4; let k = fun arg1 arg2 arg3 -> (Debug.outdent 4; k arg1 arg2 arg3) in

  let strategy = increment_depth strategy in

  dprint (fun () -> "obj_split: cPsi = " ^ P.dctxToString cO cD cPsi);
  dprint (fun () -> "--      a: " ^ R.render_cid_typ a);
  dprint (fun () -> "--  spine: " ^ P.spineToString cO cD cPsi (spine, idSub));
  Debug.indent 2; verify (ms, cO, cD, cPsi); Debug.outdent 2;
  dprnt "";

  (* PVars premises,  App<x_1> thru App<x_k> premises: *)
  let (sch_elems, concretesWithTypes) = match strategy.phase with
                                        | ContextVariablePhase -> ([], [])
                                        | ContextDependentArgumentsPhase -> ([], [])
                                        | TermPhase -> (getSchemaElems cO cPsi, getConcretesAndTypes cPsi)
  in
  
  (* App<c_1> thru App<c_n> premises: *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in

  let callAppOnPVar (LF.SchElem (some_part, typRec) as sch_elem) =
    dprint (fun () -> "checking if parameter(s) from schema element  " ^ P.schElemToString sch_elem ^ "  are covered");

    let Some psi = Context.ctxVar cPsi in
    
    let some_part_dctx = Context.projectCtxIntoDctx some_part in
    dprint (fun () -> "+++   cD =  " ^ P.mctxToString cO cD ^ "\n"
                    ^ "+++ cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                    ^ "+++ some_part_dctx = " ^ P.dctxToString cO cD some_part_dctx);

    let cPsi_just_psi = LF.CtxVar psi in

    let some_part_dctxSub_psi = Ctxsub.ctxToSub' cD cPsi_just_psi some_part_dctx in
    (* cO; cD; cPsi_just_psi |- some_part_dctxSub_psi : some_part_dctx *)
(*    let _ = Lfcheck.checkSub None cO cD cPsi_just_psi some_part_dctxSub_psi some_part_dctx in *)

    let typRec = Whnf.normTypRec (typRec, some_part_dctxSub_psi) in
    
    let id_psi = Substitution.LF.justCtxVar cPsi in
    let _ = Lfcheck.checkSub None cO cD cPsi id_psi cPsi_just_psi in

   (* cPsi |- id_psi : cPsi_just_psi |- some_part_dctxSub_psi : some_part_dctx *)

    dprnt "checkSub OK";
    
    let head = LF.PVar (LF.Offset 1, id_psi) in
      match typRec with
        | LF.SigmaLast tA ->
            begin
            dprint (fun () -> "pvar SigmaLast 00000\n"
                      ^ "cD = " ^ P.mctxToString cO cD);
            let tA' = Whnf.normTyp (tA, id_psi) in
            let name = new_parameter_name "p@" in
            let _ = dprint (fun () -> "SigmaLast: created parameter \"" ^ R.render_name name ^ "\"") in
            let pdecl  = LF.PDecl(name, tA', cPsi_just_psi) in
            let cDWithPVar = LF.Dec(cD, pdecl) in
            let cD = () in cD;
            let addPVar_msub = (*Whnf.mvar_dot1 idMSub*) LF.MShift 1 in
            let tA' = sTyp tA' addPVar_msub in
            let spine = sSpine spine addPVar_msub in
            let cPsi = sDCtx cPsi addPVar_msub in
            
            let unifyLeft = Whnf.cnormTyp (LF.Atom(loc, a, spine), idMSub) in
            let unifyRight = Whnf.cnormTyp (tA', idMSub) in
              dprint (fun () -> "pvar SigmaLast 1\n"
                        ^ "   tA' = " ^ P.typToString cO cDWithPVar cPsi (tA', idSub) ^ "\n"
                        ^ "     P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), idSub));
              if try
                   U.unifyTyp cDWithPVar(*LF.Empty*) cPsi (unifyLeft, idSub) (unifyRight, idSub);
                   true
                 with U.Unify s ->
                    (dprnt "callOnComponent: types didn't unify; last component impossible";
                     false)
              then begin
(*                let (theta, cDAbstracted) = Abstract.abstractMSub abstractor_msub  in *)
                let (theta, cDAbstracted) = (idMSub, cDWithPVar) in
                dprint (fun () -> "**** cDAbstracted = " ^ P.mctxToString cO cDAbstracted);
                let cDAbstracted = Whnf.normMCtx cDAbstracted in
                dprint (fun () -> "**** cDAbstracted = " ^ P.mctxToString cO cDAbstracted);
                                    
                let cDWithPVar = cDAbstracted in
                let cPsi = sDCtx cPsi theta in
                let spine = sSpine spine theta in
                let tA' = sTyp tA' theta in

                let ms2 = Whnf.mcomp (Whnf.mcomp ms addPVar_msub) theta in
(*                  dprnt "<<..";
                  Lfcheck.check cO cDWithPVar cPsi (LF.Root(None, head, LF.Nil), idSub) (LF.Atom(loc, a, spine), idSub);
                  dprnt ">>.."; *)
                  Debug.indent 2; dprint (fun () -> "PVars; verify, before calling app");
                    verify (ms2, cO, cDWithPVar, cPsi); Debug.outdent 2;
                  dprint (fun () -> "pvar SigmaLast 2\n"
                                  ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                  ^ "--      cPsi = " ^ P.dctxToString cO cDWithPVar cPsi ^ "\n"
                                  ^ "--       tA' = " ^ P.typToString cO cDWithPVar cPsi (tA', idSub) ^ "\n"
                                  ^ "--         P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), idSub));
                  Debug.indent 2;
                  app (strategy, ms2, cO, cDWithPVar, cPsi)
                    (head, LF.Nil, tA')
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
                dprint (fun () -> "pvar SigmaElem: sA = " ^ P.typToString cO cD cPsi sA);
                dprint (fun () -> "pvar SigmaElem: tA = " ^ P.typToString cO cD cPsi (tA, idSub));
                let tA' = Whnf.normTyp (tA, id_psi) in
                let name = new_parameter_name "p@" in
                let _ = dprint (fun () -> "SigmaElem: created parameter \"" ^ R.render_name name ^ "\"") in
                let pdecl  = LF.PDecl(name, Whnf.normTyp(LF.Sigma typRec, id_psi), cPsi_just_psi) in
                let cDWithPVar = LF.Dec(cD, pdecl) in

                dprint (fun () -> "    tA' = " ^ P.typToString cO cD cPsi (tA', idSub));

                let cD = () in cD;
                let addPVar_msub = LF.MShift 1 in

                let tA' = sTyp tA' addPVar_msub in
                dprint (fun () -> "    tA' = " ^ P.typToString cO cDWithPVar cPsi (tA', idSub));
                let spine = sSpine spine addPVar_msub in
                let cPsi = sDCtx cPsi addPVar_msub in
                
(*                let abstractor_msub = mctxToMSub cDWithPVar in *)
                
                let unifyLeft = Whnf.cnormTyp (LF.Atom(loc, a, spine), idMSub) in
                let unifyRight = Whnf.cnormTyp (tA', idMSub) in
                  if try
                    dprint (fun () -> "    unifyLeft = Atom(_, a, spine) = " ^ P.typToString cO cDWithPVar cPsi (unifyLeft, idSub));
                    dprint (fun () -> "   unifyRight = tA' = " ^ P.typToString cO cDWithPVar cPsi (unifyRight, idSub));
                    U.unifyTyp cDWithPVar(*LF.Empty*) cPsi (unifyLeft, idSub) (unifyRight, idSub);
                    true
                  with U.Unify s ->
                    begin
                      dprnt "callOnComponent: types didn't unify; this component impossible";
                      false
                    end
                  then begin
                    (*                let (theta, cDAbstracted) = Abstract.abstractMSub abstractor_msub  in *)
                    let (theta, cDAbstracted) = (idMSub, cDWithPVar) in

                    dprint (fun () -> "**** cDAbstracted = " ^ P.mctxToString cO cDAbstracted);
                    let cDAbstracted = Whnf.normMCtx cDAbstracted in
                    dprint (fun () -> "**** cDAbstracted = " ^ P.mctxToString cO cDAbstracted);

                    let cDWithPVar = cDAbstracted in
                    let cPsi = sDCtx cPsi theta in
                    let spine = sSpine spine theta in
                    let tA' = sTyp tA' theta in
                      dprint (fun () -> "pvar SigmaElem 1 (index = " ^ string_of_int index ^ ")\n"
                                      ^ "head = " ^ P.headToString cO cDWithPVar cPsi head ^ "\n"
                                      ^ "sA(UNSHIFTED) = " ^ P.typToString cO cDWithPVar cPsi sA ^ "\n"
                                      ^ "tA' = " ^ P.typToString cO cDWithPVar cPsi (tA', idSub) ^ "\n"
                                      ^ " P = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), idSub));

                    dprint (fun () -> "pvar SigmaElem 2a\n"
                                      ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n");
(*                    Lfcheck.checkTyp cO cD cPsi (tA', idSub); *)
                    dprnt "tA' OK (1)";
                    let ms2 = Whnf.mcomp (Whnf.mcomp ms addPVar_msub) theta in
                      dprint (fun () -> "pvar SigmaElem 2\n"
                                      ^ "--cDWithPVar = " ^ P.mctxToString cO cDWithPVar ^ "\n"
                                      ^ "--tA' = " ^ P.typToString cO cDWithPVar cPsi (tA', idSub) ^ "\n"
                                      ^ "-- P  = " ^ P.typToString cO cDWithPVar cPsi (LF.Atom(loc, a, spine), idSub));
(*                      Lfcheck.checkTyp cO cDWithPVar cPsi (tA', idSub);
                      dprnt "tA' OK (2)";
                      Lfcheck.checkTyp cO cDWithPVar cPsi (LF.Atom(loc, a, spine), idSub);
                      dprnt "P OK"; *)
                      Debug.indent 2;
                      app (strategy, ms2, cO, cDWithPVar, cPsi)
                        (LF.Proj(head, index), LF.Nil, tA')
                        (LF.Atom(loc, a, spine))
                        (fun arg1 arg2 arg3 ->
                           Debug.outdent 2;
                           k arg1 arg2 arg3)
                  end else ()
              in
                iterTypRec callAppOnComponent (head, (typRec, idSub))
            end

  
  and callAppOnConcrete (LF.BVar x, xTyp) =
        dprint (fun () -> "checking if bound variable \"" ^ R.render_bvar cPsi x ^ "\" is covered");
        dprint (fun () -> "--the variable's type is: " ^ P.typToString cO cD cPsi (xTyp, idSub));
        app (increment_depth strategy, ms, cO, cD, cPsi)
            (LF.BVar x, LF.Nil, xTyp)
            (LF.Atom(loc, a, spine))
            k


  and callAppOnConstructor (c, cSig) =
        dprint (fun () -> "checking if constructor \"" ^ R.render_cid_term c ^ "\" is covered");
        dprint (fun () -> "--type cSig: " ^ P.typToString cO cD cPsi (cSig, idSub));
        app (increment_depth strategy, ms, cO, cD, cPsi)
            (LF.Const c, LF.Nil, cSig)
            (LF.Atom(loc, a, spine))
            k
  in
    List.iter callAppOnConstructor constructorsWithTypes;
    List.iter callAppOnPVar sch_elems;
    List.iter callAppOnConcrete concretesWithTypes




(*
 * Obj-no-split / "MVars" rule
 *)
and obj_no_split (strategy, ms, cO, cD, cPsi) (loc, a, spine) k =
   dprnt "obj_no_split";
   Debug.indent 2;
   verify (ms, cO, cD, cPsi);
   let tP = LF.Atom(loc, a, spine) in
   let (flat_cPsi, conv_list) = flattenDCtx cPsi in  
   let s_proj   = gen_conv_sub conv_list in
   let tP' = strans_typ (tP, Substitution.LF.id) conv_list in

   let target_tP = shiftTyp tP 1 in  (* (tP, MShift 1) *)
   dprint (fun () -> "before thin: " ^ P.dctxToString cO cD flat_cPsi);

   let (thin_sub, thin_cPsi) = Subord.thin (cO, cD) (tP', flat_cPsi) in

(*
   let (thin_sub, thin_cPsi) = (Substitution.LF.id, cPsi) in
*)
   (* flat_cPsi |- thin_sub : thin_cPsi *)
   (* flat_cPsi |- tP' type              *)
   let inv_thin_sub = Substitution.LF.invert thin_sub in 
   dprint (fun () -> "s_proj: " ^ P.subToString cO cD cPsi s_proj);
   dprint (fun () -> "thin-subst.: " ^ P.subToString cO cD flat_cPsi thin_sub);
   dprint (fun () -> "tP:          " ^ P.typToString cO cD cPsi (tP, idSub));
   let tP_thinned = Whnf.normTyp (tP', inv_thin_sub) in 
   let name = new_name "NOSPLIT" in
   dprint (fun () -> "new MVar " ^ R.render_name name ^ " has type  " ^ P.typToString cO cD thin_cPsi (tP_thinned, Substitution.LF.id)
                   ^ "  in thinned context [" ^ P.dctxToString cO cD thin_cPsi ^ "]\n");
(*   let decl  = LF.MDecl(new_name "NOSPLIT", LF.TClo(tP', inv_thin_sub), thin_cPsi) in *)
   let decl  = LF.MDecl(name, tP_thinned, thin_cPsi) in 
   dprint (fun () -> "thin_sub o s_proj = " ^ P.subToString cO cD cPsi (Substitution.LF.comp thin_sub s_proj));

   dprint (fun () -> "obj_no_split -- verify ...thin_cPsi");
   verify (ms, cO, cD, thin_cPsi);
   dprint (fun () -> "obj_no_split -- verified ...thin_cPsi\n");

   let cDWithVar = LF.Dec(cD, decl) in
   let addVar_msub = LF.MShift 1 in
   let cPsi = sDCtx cPsi addVar_msub in
   
   let tR1 : LF.head = LF.MVar(LF.Offset 1, Substitution.LF.comp thin_sub s_proj)  in

   dprint (fun () -> "\nobj_no_split -- verify cDWithVar |- cPsi");
   verify (Whnf.mcomp ms addVar_msub, cO, cDWithVar, cPsi);
   dprint (fun () -> "obj_no_split -- verified cDWithVar |- cPsi\n");

   (* old code - joshua 
   let _ = dprint (fun () -> "obj_no_split:\n"
                           ^ "--cDWithVar = " ^ P.mctxToString cO cDWithVar ^ "\n"
                           ^ "--tM1 (instance) = " ^ P.normalToString cO cDWithVar cPsi (tM1, idSub) ^ "\n"
                           ^ "--tP  = " ^ P.typToString cO cDWithVar cPsi (tP, idSub) ^ "\n"
                           ^ "--tR1 = " ^ P.headToString cO cDWithVar cPsi tR1) in
   *) 
(*   print_string "*"; *)
   let tM1 = LF.Root(loc, tR1, LF.Nil) in
   dprint (fun () -> "obj_no_split:\n"
                   ^ "--cDWithVar = " ^ P.mctxToString cO cDWithVar);
   dprint (fun () -> "--tM1 (instance) = " ^ P.normalToString cO cDWithVar cPsi (tM1, idSub));
   dprint (fun () -> "--target_tP = " ^ P.typToString cO cDWithVar cPsi (target_tP, idSub));
   Debug.outdent 2;
   k (strategy, Whnf.mcomp ms addVar_msub, cO, cDWithVar, cPsi)
     tM1
     target_tP  (* tP*)



(*
 * Obj-Pi; Obj-Sigma; call to Obj-split/Obj-no-split
 *)
and obj (strategy, ms, cO, cD, cPsi) tA k =
  dprint (fun () -> "obj: " ^ "\n"
                  ^ "--tA: " ^ P.typToString cO cD cPsi (tA, idSub));
  verify (ms, cO, cD, cPsi);
  match tA with
  | LF.PiTyp ((LF.TypDecl(name, tA1) as typdecl, depend), tA2) ->   (* rule Obj-Pi *)
       dprint (fun () -> "PiTyp");
       Debug.indent 2;
(*       let hungPsi = hangDCtx shift cPsi in
       let hungA1 = hangTyp shift tA1 in *)
       let extended_cPsi = LF.DDec(cPsi, typdecl) in
         obj (strategy, idMSub, cO, cD, extended_cPsi)
             tA2
             (fun (strategy, ms', cO, cD, _extended_cPsi) tM tA2 ->
                let cPsi = sDCtx cPsi ms' in
                let tA1 = sTyp tA1 ms' in
                let typdecl = LF.TypDecl(name, tA1) in
                  k (strategy, Whnf.mcomp ms ms', cO, cD, cPsi)
                    (LF.Lam (None, name, tM))
                    (LF.PiTyp ((typdecl, depend), tA2)));
         Debug.outdent 2

  | LF.Sigma _typ_rec ->  (* rule Obj-Sigma *)
       dprint (fun () -> "coverage.ml obj Sigma case...exiting");
       exit 222

  | LF.Atom (loc, a, spine) ->    (* rule Obj-split *)
      split_switch strategy
         (begin
           (* Split *)
           fun strategy ->
             obj_split (strategy, idMSub, cO, cD, cPsi) (loc, a, spine)
               (fun (strategy', ms', cO, cD, cPsi) b c ->   (* Restore the previous strategy, including strategy.currDepth *)
                  verify (Whnf.mcomp ms ms', cO, cD, cPsi);
                  k (strategy, Whnf.mcomp ms ms', cO, cD, cPsi) b c)
          end, begin
           (* Don't split *)
           fun strategy ->
             obj_no_split (strategy, ms, cO, cD, cPsi) (loc, a, spine) k
         end)


let rec contextDep_split (strategy, ms, cO, cD, cPsi) k =
  let continue (strategy, ms, cO, cD, cPsi) k =
        k (increment_context_depth strategy, ms, cO, cD, cPsi) in
  match cPsi with
    | LF.Null -> continue (strategy, ms, cO, cD, cPsi) k
    | LF.CtxVar _ -> continue (strategy, ms, cO, cD, cPsi) k
    | LF.DDec (cPsi', LF.TypDecl (name, tConcrete)) ->
        begin
          match tConcrete with
            | LF.Atom (loc, a, spine) ->
(*                let hung_cPsi' = hangDCtx shift cPsi' in *)
                let a_kind = (Types.get a).Types.kind in

                let rec objSpine (strategy, ms2, cO, cD, cPsi') outSpine (inSpine, typ) k =
                  match (inSpine, typ) with
                    | (LF.Nil,  LF.Atom (_loc, _b, _tSpine)) ->
                        k (strategy, ms2, cO, cD, cPsi') outSpine
                    | (LF.App(tM, inTail),  LF.PiTyp((LF.TypDecl(_, type_of_tM), _depend), rightTyp)) ->
                          let pass () = objSpine (strategy, ms2, cO, cD, cPsi') (LF.App(tM, outSpine)) (inTail, rightTyp) k in
(*                          let inTail = hangSpine shift inTail in
                          let outSpine = hangSpine shift outSpine in
                          let rightTyp = hangTyp shift rightTyp in *)
                          begin match tM with
                                | LF.Lam (_loc, _name, _body)    -> (* possible -- fix (also below) *)   pass()
                                | LF.Root (_loc, LF.BVar _, _)   -> (* can't split *)  pass()
                                | LF.Root (_loc, LF.PVar _, _)   -> (* can't split *)  pass()
                                | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible *)   pass()
                                | LF.Root (_loc, LF.Proj _, _)   -> (* can't split *)  pass()
                                | LF.Root (loc, LF.Const c, innerSpine) ->
                                      objSpine (strategy, idMSub, cO, cD, cPsi') LF.Nil (innerSpine, (Constructors.get c).Constructors.typ)
                                               (fun (strategy, ms'2, cO, cD, cPsi') newInnerSpine ->
                                                  let ms3 = Whnf.mcomp ms2 ms'2 in
                                                  verify (ms3, cO, cD, cPsi');
                                                  let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                                                  let inTail = sSpine inTail ms'2 in
                                                  let outSpine = sSpine outSpine ms'2 in
                                                  let outSpine = appendToSpine outSpine newRoot in
                                                  let rightTyp = sTyp rightTyp ms'2 in
                                                    objSpine (strategy, ms3, cO, cD, cPsi') outSpine (inTail, rightTyp) k)
                                | LF.Root (loc, LF.MVar _, _) ->
                                    let originalPhase = strategy.phase in
                                    let strategy = {strategy with phase = TermPhase} in                                    
                                      obj (strategy, idMSub, cO, cD, cPsi')
                                          type_of_tM
                                          (fun (strategy, ms'2, cO, cD, _cPsi') splitM _typeOfSplitM ->
                                             let ms3 = Whnf.mcomp ms2 ms'2 in
                                             let strategy = {strategy with phase = originalPhase} in
                                             let inTail = sSpine inTail ms'2 in
                                             let outSpine = sSpine outSpine ms'2 in
                                             let outSpine = appendToSpine outSpine splitM in
                                             let rightTyp = sTyp rightTyp ms'2 in
                                               objSpine (strategy, ms3, cO, cD, cPsi') outSpine (inTail, rightTyp) k)
                          end
                
                and objSpineKind (strategy, ms2, cO, cD, cPsi') outSpine (inSpine, kind) k =
                      match (inSpine, kind) with
                      | (LF.Nil,  LF.Typ)  ->  k (strategy, ms2, cO, cD, cPsi') outSpine
                      | (LF.App(tM, inTail),  LF.PiKind((LF.TypDecl(_, type_of_tM), _depend), rightKind))  ->
                          let pass () = objSpineKind (strategy, ms2, cO, cD, cPsi') (LF.App(tM, outSpine)) (inTail, rightKind) k in
(*                          let inTail = hangSpine shift inTail in
                          let outSpine = hangSpine shift outSpine in *)
                          begin match tM with
                                | LF.Lam (_loc, _name, _body)    -> (* possible -- fix (also above) *)   pass()
                                | LF.Root (_loc, LF.BVar _, _)   -> (* can't split *)  pass()
                                | LF.Root (_loc, LF.PVar _, _)   -> (* can't split *)  pass()
                                | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible *)   pass()
                                | LF.Root (_loc, LF.Proj _, _)   -> (* can't split *)  pass()
                                | LF.Root (loc, LF.Const c, innerSpine) ->
                                      objSpine (strategy, idMSub, cO, cD, cPsi') LF.Nil (innerSpine, (Constructors.get c).Constructors.typ)
                                               (fun (strategy, ms'2, cO, cD, cPsi') newInnerSpine ->
                                                  let ms3 = Whnf.mcomp ms2 ms'2 in
                                                  verify (ms3, cO, cD, cPsi');
                                                  let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                                                  let inTail = sSpine inTail ms'2 in
                                                  let outSpine = sSpine outSpine ms'2 in
                                                  let outSpine = appendToSpine outSpine newRoot in
                                                    objSpineKind (strategy, ms3, cO, cD, cPsi') outSpine (inTail, rightKind) k)

                                | LF.Root (loc, LF.MVar (_, mvarsub), _) ->
                                    dprint (fun () -> "CRITICAL POINT: incoming cPsi' is [" ^ P.dctxToString cO cD cPsi' ^ "];\n"
                                                    ^ "                mvarsub is  " ^ P.subToString cO cD cPsi' mvarsub);
                                    let originalPhase = strategy.phase in
                                    let strategy = {strategy with phase = TermPhase} in (* splitting depth off? *)
                                       obj (strategy, idMSub, cO, cD, cPsi')
                                           type_of_tM
                                           (fun (strategy, ms'2, cO, cD, cPsi') splitM _typeOfSplitM ->
                                              let ms3 = Whnf.mcomp ms2 ms'2 in
                                              let strategy = {strategy with phase = originalPhase} in
                                              let inTail = sSpine inTail ms'2 in
                                              let outSpine = sSpine outSpine ms'2 in
                                              let outSpine = appendToSpine outSpine splitM in
                                                objSpineKind (strategy, ms3, cO, cD, cPsi') outSpine (inTail, rightKind) k)
                          end
                in
                  objSpineKind (strategy, idMSub, cO, cD, cPsi') LF.Nil (spine, a_kind)
                    (fun (strategy, ms', cO, cD, _cPsi') splitSpine ->
                       let cPsi' = sDCtx cPsi' ms' in
                          contextDep (strategy, Whnf.mcomp ms ms', cO, cD, cPsi')
                             (fun (strategy, ms'', cO, cD, new_cPsi') ->
                                verify (ms'', cO, cD, new_cPsi');
                                let splitTypDecl = LF.TypDecl (name, LF.Atom (loc, a, splitSpine)) in
                                let reconstitutedPsi = LF.DDec (new_cPsi', splitTypDecl) in
                                  dprint (fun () -> "* splitTypDecl in \"" ^ R.render_name name ^ "\": "
                                                  ^ P.dctxToString cO cD reconstitutedPsi ^ " |- " ^ "___ " ^ P.spineToString cO cD reconstitutedPsi (splitSpine, idSub));
                                  verify (ms'', cO, cD, reconstitutedPsi);
                                  dprnt "done...";
                                  continue (strategy, ms'', cO, cD, reconstitutedPsi) k))

            | whatever ->
                contextDep (strategy, idMSub, cO, cD, cPsi')
                  (fun (strategy, ms', cO, cD, new_cPsi') ->
                     verify (Whnf.mcomp ms ms', cO, cD, new_cPsi');
                     let tConcrete = sTyp tConcrete ms' in
                       continue (strategy, Whnf.mcomp ms ms', cO, cD, LF.DDec (new_cPsi', LF.TypDecl (name, tConcrete))) k)
        end


and contextDep (strategy, ms, cO, cD, cPsi) k =
    Debug.indent 2;
    contextDep_split_switch strategy
       (begin
         (* Split *)
         fun strategy -> 
          contextDep_split (strategy, ms, cO, cD, cPsi)
            (fun (strategy', ms, cO, cD, cPsi) ->
               verify (ms, cO, cD, cPsi);
               Debug.outdent 2;
               (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, ms, cO, cD, cPsi))
        end, begin
         (* Don't split *)
         fun strategy ->
           Debug.outdent 2;
           verify (ms, cO, cD, cPsi);
           k (strategy, ms, cO, cD, cPsi)
       end)


let rec context_split (strategy, ms, cO, cD, cPsi) k =
  let strategy = increment_context_variable_depth strategy in

  (* If cPsi = g, cConcrete where g's schema is (tA1 + tA2 + ...) then:
     Call `context' with cPsi := g, _:tA1, cConcrete
     then with cPsi := g, _:tA2, cConcrete
     etc.
  *)

  let replace (replacement, psi) cPsi =
    let LF.CtxOffset psi_offset = psi in
    let (_cO, csub) = Ctxsub.inst_csub replacement psi_offset (Ctxsub.id_csub cO) cO in
      Ctxsub.ctxnorm_dctx (cPsi, csub)
  in
  let check psi (LF.SchElem(some_part_ctx, schema_rec)) =
    (* let cD2 = some_part_ctx, converted to mctx;
       let cDMerged = cD2 appended to cD;
       add appropriately to shift;
       shift cPsi
    *)
    let cPsi_just_psi = LF.CtxVar psi in
    let dctx = Context.projectCtxIntoDctx some_part_ctx in
    let dctxSub = Ctxsub.ctxToSub' cD cPsi_just_psi dctx in
    let schema_rec = Whnf.normTypRec (schema_rec, dctxSub) in
    let tA = match schema_rec with LF.SigmaLast tOnly -> tOnly 
                                 | typ_rec -> LF.Sigma typ_rec in
    let name = new_name "ctxvarsplit" in
    let new_typ_decl = LF.TypDecl(name, tA) in
    let _ = dprint (fun () -> "context_split: new concrete declaration "
                            ^ R.render_name name ^ " : " ^ P.typToString cO cD cPsi (tA, idSub)) in

    let replacement = LF.DDec (LF.CtxVar psi, new_typ_decl) in
    let cPsi_split = replace (replacement, psi) cPsi in
      context (strategy, ms, cO, cD, cPsi_split) k    
  in
  let split sch_elems = match sch_elems with
    | [] ->
        context (strategy, ms, cO, cD, cPsi) k
    | elems ->
        let Some psi = Context.ctxVar cPsi in
          List.iter (check psi) elems;
          context (strategy, ms, cO, cD, replace (LF.Null, psi) cPsi) k
  in
    split (getSchemaElems cO cPsi)


and context (strategy, ms, cO, cD, cPsi) k =
   (Debug.indent 2;
    context_split_switch strategy
       (begin
         (* Split *)
         fun strategy -> 
          context_split (strategy, ms, cO, cD, cPsi)
            (fun (strategy', ms, cO, cD, cPsi) ->   (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, ms, cO, cD, cPsi))
        end, begin
         (* Don't split *)
         fun strategy ->
           dprint (fun () -> "strategy.phase := ContextDependentArgumentsPhase");
           let strategy = {strategy with phase = ContextDependentArgumentsPhase} in
             contextDep (strategy, ms, cO, cD, cPsi) k
       end);
    Debug.outdent 2)


(*
 * covered_by  BranchBox(cO', cD', (cPsi', tR', msub', csub'), _body) (cO, cD, cPsi) tM tA
 *
 * Succeeds iff the term   cD; cPsi |- tM   is covered by   cD'; cPsi' |- tR'
 *)
let covered_by branch (cO, cD, cPsi) tM tA =
  covby_counter := !covby_counter + 1;
  match branch with
  | BranchBox (cO', cD', (cPsi', EmptyPattern, msub', csub')) ->
      raise (NoCover (fun () -> "EmptyPattern"))

  | BranchBox (cO', cD', (cPsi', NormalPattern (tR', _body), msub', csub')) ->
      (* under cO / cO' ?
         Pi cD. box(?. tM) : tA[cPsi]  =.  Pi cD'. box(?. tR') : ?[?]   *)
      dprnt "covered_by";
      Debug.indent 2;
      dprint (fun () -> "--cPsi' = " ^ P.dctxToString cO' cD' cPsi' ^ "\n"
                      ^ "--  tR' = " ^ P.normalToString cO' cD' cPsi' (tR', idSub) ^ "\n"
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
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', idSub)) in *)
(* let _mt1' = Whnf.cnormMSub mt in *)
      let cPsi' = Ctxsub.ctxnorm_dctx (cPsi', ct1) in
      
      let shift_unprimed = LF.MShift (Context.length cD') in
      let tM_shifted = Whnf.cnorm (tM, shift_unprimed)  in
      
      let _ = dprint (fun () -> P.octxToString cO ^ " |- Pi " ^ P.mctxToString cO cD
                    ^ " box(Psihat. " ^ P.normalToString cO cDConjoint cPsi (tM_shifted, idSub)
                    ^ ") : " ^ P.typToString cO cD cPsi (tA, idSub)
                    ^ "["    ^ P.dctxToString cO cD cPsi ^ "]") in
      let _ = dprnt  (" COVERED-BY ") in
      let _ = dprint (fun () -> P.octxToString cO' ^ " |- Pi " ^ P.mctxToString cO' cD'
                              ^ " box(" ^ P.dctxToString cO' cD' cPsi' ^ " . " ^ ""
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', idSub)
                              ^ ") : " ^ P.msubToString cO' cD' msub'
                              ^ "[" ^ P.csubToString cO' cD' csub' ^ "]") in
      let matchD = cDConjoint in
      let matchPsi = cPsi' in
      let matchLeft = (tM_shifted, idSub) in
      let matchRight = (tR', idSub) in
      
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
        
        U.disallowUndefineds (fun () ->
                                U.matchTerm matchD matchPsi matchLeft matchRight);
        
        dprint (fun () -> "MATCHED");
        Debug.outdent 2
      with U.Unify s -> (dprnt "no match";
                         Debug.outdent 2;
                         raise (NoCover (fun () -> "---inner NoCover escaped---")))



let rec covered_by_set branches (strategy, ms, cO, cD, cPsi) tM tA =
  verify (ms, cO, cD, cPsi);
  match branches with
  | [] -> raise (NoCover (fun () -> "Not covered: "
                                  ^ "[" ^ P.dctxToString cO cD cPsi ^ "]  "
                                  ^ P.normalToString cO cD cPsi (tM, idSub)))
  | branch :: branches ->
      try covered_by branch (cO, cD, cPsi) tM tA;
        dprint (fun () -> "Term covered:  " ^ P.normalToString cO cD cPsi (tM, idSub)
                  ^ "  covered by  "
                  ^ match branch with BranchBox (cO', cD', (cPsi', NormalPattern (tR', _body), _msub', _csub')) ->
                          P.normalToString cO' cD' cPsi' (tR', idSub))
      with NoCover _ -> covered_by_set branches (strategy, ms, cO, cD, cPsi) tM tA


let rec maxSpine low f = function
  | LF.Nil -> low
  | LF.App(tM, spine) ->
      let f_tM = f tM in
        max f_tM (maxSpine f_tM f spine)

let rec maxTuple f = function
  | LF.Last tM -> f tM
  | LF.Cons(tM, tuple) -> max (f tM) (maxTuple f tuple)

and depth = function
  | LF.Lam(_, _, tM) -> 1 + depth tM   (* should probably just be   depth tM   -jd *)
  | LF.Root(_, head, spine) -> 1 + (maxSpine (depthHead head) depth spine)
  | LF.Clo(tM, _) -> depth tM
  | LF.Tuple(_, tuple) -> 1 + maxTuple depth tuple

and depthHead = function
  | LF.BVar _ -> 1
  | LF.Const _ -> 1
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
  | BranchBox (_cO', _cD', (_cPsi', EmptyPattern, _msub', _csub')) ->
      1 + 1

  | BranchBox (_cO', _cD', (_cPsi', NormalPattern (tM', _body), _msub', _csub')) ->
      1 + depth tM'

let length_branch cPsi = function
  | BranchBox (_cO', _cD', (cPhi', _pattern, _msub', _csub')) ->
      Context.dctxLength cPhi' - Context.dctxLength cPsi

let dependentDepth_branch = function
  | BranchBox (_cO', _cD', (cPhi', _pattern, _msub', _csub')) ->
      dependentDepth_dctx cPhi'

(* Lifted to (branch list) *)
let maxDepth branches = maxfun depth_branch branches
let maxContextVariableDepth cPsi branches = maxfun (length_branch cPsi) branches
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
      let cutoff = max 1 (maxDepth problem.branches + !extraDepth)
      and variableDepth = maxContextVariableDepth cPsi problem.branches
      and dep = maxDependentDepth problem.branches
      in
      let _ = dprint (fun () -> "cutoff depth                = " ^ string_of_int cutoff) in
      let _ = dprint (fun () -> "max context variable depth  = " ^ string_of_int variableDepth) in
      let _ = dprint (fun () -> "max dependent depth         = " ^ string_of_int dep) in
      let strategies = tabulate cutoff (fun depth -> naive_strategy (depth, variableDepth, dep)) in
        try
          dprint (fun () -> "Coverage checking a case with "
                          ^ string_of_int (List.length problem.branches) ^ " branch(es) at:\n"
                          ^ Pretty.locOptToString problem.loc);
          tryList
            (fun strategy ->
               Debug.pushIndentationLevel();
               dprint (fun () -> "trying strategy " ^ strategyToString strategy);
               begin try
                 original_cD_length := Context.length problem.cD;
(*                 let tA = hangTyp shift tA in *)
                   context (strategy, idMSub, problem.cO, problem.cD, cPsi)
                     (fun (strategy, ms', cO, cD, cPsi) ->
                        dprint (fun () -> "context generated cPsi = " ^ P.dctxToString cO cD cPsi);
                        dprint (fun () -> "strategy.phase := ContextDependentArgumentsPhase");
                        let strategy = {strategy with phase = ContextDependentArgumentsPhase} in
                        let tA = sTyp tA ms' in
                          contextDep (strategy, ms', cO, cD, cPsi)
                            (fun (strategy, ms'', cO, cD, cPsi) ->
                               dprint (fun () -> "context generated cPsi = " ^ P.dctxToString cO cD cPsi);
                               dprint (fun () -> "strategy.phase := TermPhase");
                               let strategy = {strategy with phase = TermPhase} in
                               obj (strategy, ms'', cO, cD, cPsi)
                                   tA
                                   (covered_by_set problem.branches)))
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
