(** Coverage checker

   @author Joshua Dunfield
   modified: Brigitte Pientka
*)

let nn = ref 0


(* Coverage has 3 phases:
 
    1. ContextVariablePhase:
         possibly split context variables
  
    2. ContextDependentArgumentsPhase:
         possibly split on arguments to dependent types in the context
 
    3. TermPhase:
         possibly split the object (term)
 
   The LFMTP '08 paper only describes phase 3 (TermPhase).
   
   In each phase, splitting is limited by a maximum depth
   (phase 1: maxContextVariableDepth; phase 2: maxContextDepth; phase 3: maxDepth).
   These maximums are computed from the branches, as follows:

   1. ContextVariablePhase: the length of the longest context in a branch,
        less the length of the scrutinee's context.  For example:
        
             case e of     % e : term[g, x:nat]
               [g, y:nat, x:nat] pat1 => ...
             | [g, z:nat, y:nat, x:nat] pat2 => ...
             | [g, x:nat] pat3 =>

       Here, the second branch is the longest with 3 bound variable declarations, but
       `g' only needs to be split twice, since x:nat is already in the type of e:

           length of longest context - length of scrutinee context = 3 - 1 = 2.
   
   2. ContextDependentArgumentsPhase: the depth of the deepest dependent type in a
        branch context.  [to be described]

   3. TermPhase: the depth of the deepest pattern in a branch.  Example:

             case e of
               [g] U .. => ...

       There is no need to split; the computed depth is 0.

             case e of
               [g] #p .. => ...
             | [g] U .. => ...
       
       There is still no need to split, since the case U .. covers everything, but the depth
       of the pattern  #p ..  is 1, so the computed depth is 1.

             case e of
               [g] succ (succ (succ zero)) => ...
             | [g] U .. => ...

       Again there is no need to split, but the depth of the first pattern is

              depth(zero) + 1 + 1 + 1 = 1 + 3 = 4

       so the computed depth is 4.
       
       Currently, 1 is added to the term depth; this is needed for some examples,
       but it is not understood why.  Thus, the depth used for the first example
       ([g] U ..) is 1, not 0.
  
   Coverage consists of a series of searches; if any search succeeds, then coverage
   succeeds.
   Even when the computed term depth is quite high, coverage first tries using
   a lower search depth, starting with 0.  Thus, for the [g] succ (succ (succ zero)) example,
   coverage will succeed very quickly because of the [g] U .. branch.  If coverage
   cannot be shown, the maximum search depth is increased by 1 until it reaches the
   computed term depth.  If coverage cannot be shown even at the computed term depth,
   coverage fails entirely.

   During each search, the decision of whether or not to split is made as follows:

     - If the current depth is >= the maximum depth for this search (which, again,
         could be less than the computed term depth), do not split; try to show coverage
         for a meta-variable (e.g., for the first example show that [g] NOSPLIT1 .. is covered).
         Otherwise:

     - Try not splitting -- perhaps we don't need to split at this point, and it saves a lot of
        time if we don't.  If we can't show coverage (exception NoCover raised), then split.
   
   For a pattern of an n-ary constructor, coverage traverses the term from left to right.
   Since we attempt to show coverage without splitting, and then backtrack to the last
   choice point, we effectively split from right to left.  For example, given a constructor

      add : nat -> nat -> nat.

   then we first try to show that  [g] add (NS1 ..) (NS2 ..)  is covered.  If this fails, the last
   choice was on whether to split NS2, so we next try to show that

           add (NS1 ..) (#p ..)
           add (NS1 ..) zero
           add (NS1 ..) (succ (NS3 ..))
           add (NS1 ..) (add (NS4 ..) (NS5 ..))

   are covered.  But say that all of these fail, because we didn't split NS1.  So after
   generating all the above, we discard them and return to split NS1:

           add (#p ..) (NS6 ..)
           add zero (NS6 ..)
           add (succ (NS7 ..)) (NS6 ..)
           add (add (NS8 ..) (NS9 ..)) (NS6 ..)

   Now for each of these splits, we will try to show coverage without splitting NS6,
   but if necessary will split it as well.  In the worst case we have to show that each of
   the 16 combinations of the arguments splits.
*)



open Syntax.Int
open Syntax.Int.Comp

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


let noop_shift = {
  n = 0
}

let sHead head msub =
  let root = LF.Root(None, head, LF.Nil) in
    match Whnf.cnorm (root, msub) with
      | LF.Root(_, head, LF.Nil) -> head
      | _ -> (print_string "broken (coverage.ml)\n"; exit 88)
        
let sSpine spine msub = Whnf.cnormSpine (spine, msub)
let sNormal tM msub = Whnf.cnorm (tM, msub)
let sTyp tA msub = Whnf.cnormTyp (tA, msub)
let sDCtx cPsi msub = Whnf.cnormDCtx (cPsi, msub)


(* Invariants of the 5-tuple (strategy, cs, ms, cO, cD, cPsi):
   
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

let verify (cs, ms, cO, cD, cPsi) =
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


(* strengthen_mctx cD = (cD' , msub)

   cD |- msub : cD'
*)
let rec strengthen_mctx cD =
  let rec str_mctx cD0 k = match cD0 with
    | LF.Empty -> (LF.Empty, LF.MShift k )
    | LF.Dec(cD0', LF.MDecl (u, tA, cPsi)) -> 
	let (cD', ms') = str_mctx cD0' (k+1) in  
	begin match Context.dctxToHat cPsi with
	  | (None, _ ) -> (LF.Dec(cD', LF.MDecl(u, tA, cPsi)), LF.MDot(LF.MV (k+1), ms'))
	  | ( _  , _ ) -> (cD', ms')
	end 
    | LF.Dec(cD0', LF.PDecl (u, tA, cPsi)) -> 
	let (cD', ms') = str_mctx cD0' (k+1) in  
	begin match Context.dctxToHat cPsi with
	  | (None, _ ) -> (LF.Dec(cD', LF.PDecl(u, tA, cPsi)), LF.MDot(LF.MV (k+1), ms'))
	  | ( _  , _ ) -> (cD', ms')
	end 
  in 
    str_mctx cD 0



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

let new_strategy (depth, contextVariableDepth, contextDepth) =
      {maxDepth = depth ;
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
let extraDepth = ref 1          (* amount of split depth, in addition to the supposedly adequate amount *)
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
let idCSub = LF.CShift 0


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
   cO ; cD ; cPsi |- h spine : tA0
   k is the continuation J
*)
let rec app (strategy, (cs : LF.csub), (ms : LF.msub), cO, cD, cPsi) (h, spine, tA0) tP k =
  let _ = dprint (fun () -> "App:   h  = " ^ P.headToString cO cD cPsi h ^ "\n"
                          ^ "App: tA0 = " ^ P.typToString cO cD cPsi (tA0, idSub) ^ "\n"
                          ^ "App: tP  = " ^ P.typToString cO cD cPsi (tP, idSub) ^ "\n"
                          ^ "   in cPsi = " ^ P.dctxToString cO cD cPsi ) in
  Lfcheck.checkTyp cO cD cPsi (tA0, idSub);
  dprnt "checkTyp tA0 OK";
  Lfcheck.checkTyp cO cD cPsi (tP, idSub);
  dprnt "checkTyp tP OK";
(*  always fails because not eta-expanded
   Lfcheck.check cO cD cPsi (LF.Root(None, h, spine), idSub) (tA0, idSub);
  dprnt "check OK";
*)
  match tA0 with
  | LF.PiTyp (((LF.TypDecl(x, tA1)) as x_decl, _depend), tA2) ->   (* rule App-Pi *)
      let cPsi_x = LF.DDec(cPsi, x_decl) in
      let _ = dprint (fun () -> "App-Pi: tA = PiTyp(" ^ R.render_name x ^ ":"
                                   ^ P.typToString cO cD cPsi (tA1, idSub) ^ "), \n                    "
                                   ^ P.typToString cO cD cPsi_x (tA2, idSub) ^ ")") in
(*      let _ = dprint (fun () -> "App-Pi(0): tA2 = " ^ P.typToString cO cD cPsi_x (tA2, idSub)) in  *)
      let _ = dprint (fun () -> "App-Pi: calling obj to generate instances of "
                        ^ P.typToString cO cD cPsi (tA1, idSub)) in
      obj (strategy, idCSub, idMSub, cO, cD, cPsi) tA1
        (fun (strategy, cs, ms', cO, cD, cPsi) tM _tA1 ->
(*           let ms = Substitution.LF.comp ms' ms in *)
           let LF.Root(None, h', spine') = Whnf.cnorm (LF.Root(None, h, spine), ms') in
           let tA2 = Whnf.cnormTyp (tA2, ms') in
           let tP' =  Whnf.cnormTyp (tP, ms')  in
           let _ = dprint (fun () -> "App-Pi(tM):    " ^ P.normalToString cO cD cPsi (tM, idSub)) in
(*           let _ = dprint (fun () -> "App-Pi(tA2)SH: " ^ 
	     P.typToString cO cD cPsi_x (tA2, idSub)) in *)
           let substitution = LF.Dot(LF.Obj tM, (*Substitution.LF.identity cPsi*)idSub) in 
           let _ = dprint (fun () -> "substitution:  " ^ 
			     P.subToString cO cD cPsi substitution) in
           let tA2_tM = Whnf.normTyp (tA2, substitution) in

           let _ = dprint (fun () -> "App-Pi(1):     " ^   P.typToString cO cD cPsi (tA2_tM, idSub)) in
           let _ = Lfcheck.checkTyp cO cD cPsi (tA2_tM, idSub) in 
           let _ = dprint (fun () -> "App-Pi(h):    " ^    P.headToString cO cD cPsi h') in
           let _ = dprint (fun () -> "App-Pi(spine): " ^   P.spineToString cO cD cPsi (spine', idSub)) in
           let _ = dprint (fun () -> "App-Pi(tP):    " ^   P.typToString cO cD cPsi (tP', idSub)) in
           app (strategy, cs, 
                Whnf.mcomp ms ms',  (* continue from the original cD_orig *)
                cO, 
                cD, 
                cPsi)
               (h',
                appendToSpine spine' tM,
                tA2_tM)
                tP'
               k)

  | LF.Sigma typRec ->     (* rule App-Sigma *)
      begin
        (* cO ; cD ; cPsi |- sA : type *)
        let appSigmaComponent (sA, index) =
          let tA = Whnf.normTyp sA in
            dprint (fun () -> "App-Sigma 1 (index = " ^ string_of_int index ^ ")\n"
                            ^ "--cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                            ^ "--  h = " ^ P.headToString cO cD cPsi h ^ "\n"
                            ^ "--  sA = " ^ P.typToString cO cD cPsi sA ^ "\n"
                            ^ "--  tA = " ^ P.typToString cO cD cPsi (tA, idSub) ^ "\n"
                            ^ "--  tP = " ^ P.typToString cO cD cPsi (tP, idSub));
          let msub_ref = mctxToMSub cD in
          let unifyLeft  = (Whnf.cnormTyp (tP, msub_ref), idSub) in
          let unifyRight = (Whnf.cnormTyp (tA, msub_ref), idSub) in
	  let cPsi_ref   = Whnf.cnormDCtx (cPsi, msub_ref) in 
          if try
            (* XXX Broken : Tue Sep  7 09:54:40 2010 -bp 
		              Corrected some of the typing invariants.
		              but no example to really test it *)
            U.unifyTyp LF.Empty cPsi_ref unifyLeft unifyRight;
            true
          with U.Unify s ->
            (dprnt "appSigmaComponent unify error; this component impossible";
              false
	    )
          then 
            (let (theta, cD') = 
	       (try Abstract.abstractMSub (Whnf.cnormMSub msub_ref )
		with Abstract.Error s -> 
		  raise (NoCover (fun () -> "Abstraction failed: " ^ s ^ 
				    "\n This indicates that generated patterns contained unification-problems outside the decidable pattern fragment; \n there are two solutions: try setting the coverage depth higher or prove by hand that some cases are impossible") )) in
             let cPsi' = Whnf.cnormDCtx (cPsi, theta) in
             let LF.Root(None,h', _ ) = Whnf.cnorm (LF.Root(None, h, LF.Nil),  theta) in
             let tA' = Whnf.cnormTyp (tA, theta) in
             let tP' = Whnf.cnormTyp (tP, theta) in
            
               dprint (fun () -> "App-Sigma 2a\n"
                          ^ "--cD'    = " ^ P.mctxToString cO cD' ^ "\n"
                          ^ "--tA'    = " ^ P.typToString cO cD' cPsi' (tA', idSub) 
			  ^ "\n"
                          ^ "--tP'    = " ^ P.typToString cO cD' cPsi' (tP', idSub));
               app (strategy, cs, Whnf.mcomp ms theta, cO, cD', cPsi')
                    (LF.Proj(h', index), LF.Nil, tA')
                    tP'
                 k
              )
	  else ()
        in
          iterTypRec appSigmaComponent (h, (typRec, idSub))
      end

  | LF.Atom(loc, a, typeSpine) as tQ ->
      begin
        dprnt "Entering LF.Atom case of app";
        Debug.indent 2;
        dprint (fun () -> "tA0=tQ atomic; \n    cD = " ^ P.mctxToString cO cD
                        ^ "\n  cPsi = " ^ P.dctxToString cO cD cPsi
                        ^ "\n  TERM = " ^ P.normalToString cO cD cPsi (LF.Root(None, h, spine), idSub)
                        ^ "\n   tA0 = " ^ P.typToString cO cD cPsi (tA0, idSub)
                        ^ "\n   tP  = " ^ P.typToString cO cD cPsi (tP, idSub));
        Lfcheck.check cO cD cPsi (LF.Root(None, h, spine), idSub) (tA0, idSub);   (* used to break for test/cd2.bel*)
        dprnt "Lfcheck.check against tA0 (a.k.a. tQ) OK";
        let msub_ref = mctxToMSub cD in
          dprint (fun () -> "LF.Atom tQ = " ^ P.typToString cO cD cPsi (tQ, idSub));
        let unifyLeft =  (Whnf.cnormTyp (tQ, msub_ref), idSub) in
        let unifyRight = (Whnf.cnormTyp (tP, msub_ref), idSub) in
          dprint (fun () -> "LF.Atom tP = " ^ P.typToString cO cD cPsi (tP, idSub));
          dprint (fun () -> "App-??unify:  " ^ P.typToString cO cD cPsi unifyLeft ^ "  =?=  "
                             ^ P.typToString cO cD cPsi unifyRight);
        let cPsi_ref = Whnf.cnormDCtx (cPsi, msub_ref) in 
        try
          U.unifyTyp LF.Empty  cPsi_ref unifyLeft unifyRight;
          dprint (fun () -> "[AFTER UNIFYTYP]\n unifyLeft = " ^ P.typToString cO LF.Empty cPsi_ref unifyLeft );
          dprint (fun () -> "unifyRight = " ^ P.typToString cO LF.Empty cPsi_ref unifyRight );
          Debug.outdent 2;
          let (theta, cD') = (try Abstract.abstractMSub (Whnf.cnormMSub msub_ref)
			      with Abstract.Error s -> 
				raise (NoCover (fun () -> "Abstraction failed: " ^ s ^ 
				    "\n This indicates that generated patterns contained unification-problems outside the decidable pattern fragment; \n there are two solutions: try setting the coverage depth higher or prove by hand that some cases are impossible"
					       ))) in
          let cPsi'  = Whnf.cnormDCtx (cPsi, theta) in
          let tR'    = Whnf.cnorm (LF.Root (loc, h, spine), theta) in 
	  (* let tP'    = Whnf.cnormTyp (tP, theta) in  *)
	  let tQ'    = Whnf.cnormTyp(tQ, theta) in (* tP' = tQ' by invariant *)
            k (strategy, cs, Whnf.mcomp ms theta, cO, cD', cPsi') tR' tQ' (* tP_uninst *)
			       
        with
          U.Unify s ->   (* rule App-slashunify *)
            (dprint (fun () -> "Type  " ^ P.typToString cO LF.Empty cPsi_ref unifyLeft ^ "  does not unify with  "
                             ^ P.typToString cO LF.Empty cPsi_ref unifyRight ^ ";");
             dprint (fun () -> " ignoring  " ^ P.headToString cO cD cPsi h ^ "  as impossible");
             Debug.outdent 2;
             ()  (* succeed *))
      end



(* obj_split:   Obj-split rule (Fig. 6)
 *)
and obj_split (strategy, (cs : LF.csub), (ms : LF.msub), cO, cD, cPsi) (loc, a, spine) k =
(*  (
    print_string"*";
   (if !nn mod 80 = 0 then print_string ("\n" ^ R.render_cid_typ a ^ " . " ^ P.spineToString cO cD cPsi (spine, idSub)));
   (if !nn mod 20 = 0 then flush_all());
   nn := !nn + 1
  ); *)
  Debug.indent 4; let k = fun arg1 arg2 arg3 -> (Debug.outdent 4; k arg1 arg2 arg3) in

  let strategy = increment_depth strategy in

  dprint (fun () -> "obj_split: in cPsi = " ^ P.dctxToString cO cD cPsi);
  dprint (fun () -> "--      a: " ^ R.render_cid_typ a);
  dprint (fun () -> "--  spine: " ^ P.spineToString cO cD cPsi (spine, idSub));
  Debug.indent 2; verify (cs, ms, cO, cD, cPsi); Debug.outdent 2;
  dprnt "";

  (* PVars premises,  App<x_1> thru App<x_k> premises: *)
  let (sch_elems, concretesWithTypes) = 
    match strategy.phase with
      | ContextVariablePhase -> ([], [])
      | ContextDependentArgumentsPhase -> ([], [])
      | TermPhase -> (getSchemaElems cO cPsi, getConcretesAndTypes cPsi)
  in
  
  (* App<c_1> thru App<c_n> premises: *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in

  (* callAppOnPVar :  cO             |- cs : cO'
                      cO ; cD        |- ms : cD'
                      cO ; cD ; cPsi |- a spine : type
  *)
  let callAppOnPVar (LF.SchElem (some_part, typRec) as sch_elem) =
    dprint (fun () -> "checking if parameter(s) from schema element  " 
	             ^ P.schElemToString sch_elem ^ "  are covered");

    let Some psi = Context.ctxVar cPsi in
    
    let dctx = Context.projectCtxIntoDctx some_part in
    dprint (fun () -> "+++   cD =  " ^ P.mctxToString cO cD ^ "\n"
                    ^ "+++ cPsi = " ^ P.dctxToString cO cD cPsi ^ "\n"
                    ^ "+++ dctx = " ^ P.dctxToString cO LF.Empty dctx);

    let cvar_psi = LF.CtxVar psi in

    let (cD_ext, dctxSub, offset) = Ctxsub.ctxToSub_mclosed cD cvar_psi dctx in
    (* cO; cD_ext; psi |- dctxSub : dctx  *)
    let typRec = Whnf.normTypRec (typRec, dctxSub) in
    (* cO ; cD_ext ; psi |- typRec *)
    let _      = dprint (fun () -> "typRec = " ^ P.typRecToString cO cD_ext cvar_psi (typRec, idSub)) in 
    let cPsi'  = Whnf.cnormDCtx (cPsi, LF.MShift offset) in 
    let id_psi = Substitution.LF.justCtxVar cPsi' in   
    let _ = Lfcheck.checkSub None cO cD_ext cPsi' id_psi cvar_psi in 

   (* cO ; cD_ext        ; cPsi' |- id_psi : cvar_psi 
      cO ; cD_ext, pdecl ; cPsi' |- id_psi : cvar_psi 
      cO ; cD_ext ; cvar_psi |- dctxSub : dctx *)
    dprnt "checkSub OK";

    let head = LF.PVar (LF.Offset 1, id_psi) in
      match typRec with
      | LF.SigmaLast tA ->
       (dprint (fun () -> "pvar SigmaLast 00000\n" ^ "cD = " ^ P.mctxToString cO cD);
        let tA' = Whnf.normTyp (tA, id_psi) in   
          (* cO ; cD_ext ; cPsi' |- tA : type *)
        let name = new_parameter_name "p@" in
        let _ = dprint (fun () -> "SigmaLast: created parameter \"" ^ R.render_name name ^ "\"") in
        let pdecl  = LF.PDecl(name, tA, cvar_psi) in
        let cD_ext_pdecl = LF.Dec(cD_ext, pdecl) in
	let _ = dprint (fun () -> "cD_ext_pdecl = " ^ P.mctxToString cO cD_ext_pdecl )in
        let tA'    = Whnf.cnormTyp (tA', LF.MShift 1)  in
        let spine'  = Whnf.cnormSpine (spine, LF.MShift (offset + 1)) in
        let cPsi'  = Whnf.cnormDCtx (cPsi', LF.MShift 1) in
        (*   cO ; cD_ext, pdecl  |- cPsi' dctx
             cO ; cD_ext, pdecl ; cPsi' |- tA'     : type
             cO ; cD_ext, pdecl ; cPsi' |- a spine : type
        *)
        let msub_ref  = Ctxsub.mctxToMSub cD_ext_pdecl in
        let unifyLeft = Whnf.cnormTyp (LF.Atom(loc, a, spine'), msub_ref) in
        let unifyRight = Whnf.cnormTyp (tA', msub_ref) in
        let cPsi_inst  = Whnf.cnormDCtx (cPsi', msub_ref) in 
          dprint (fun () -> "pvar SigmaLast 1\n"
		    ^ "   tA' = " ^ P.typToString cO LF.Empty cPsi_inst (unifyRight, idSub) ^ "\n"
		    ^ "     P = " ^ P.typToString cO LF.Empty cPsi_inst (unifyLeft, idSub));
        if (try
              (* check whether the pvar's type is compatible with the 
		 target-type of the pattern, i.e. if this pvar is a 
		 valid pattern of the target-type *)
	      U.unifyTyp LF.Empty cPsi_inst (unifyLeft, idSub) (unifyRight, idSub);
	      true
	    with U.Unify s ->
	      (dprnt "callOnComponent: types didn't unify; last component impossible";
	       false)
	   )
        then 
          (let (theta, cD'_ext) = 
	     (try Abstract.abstractMSub (Whnf.cnormMSub msub_ref)  
	      with Abstract.Error s -> 		  raise (NoCover (fun () -> "Abstraction failed: " ^ s ^ 
				    "\n This indicates that generated patterns contained unification-problems outside the decidable pattern fragment; \n there are two solutions: try setting the coverage depth higher or prove by hand that some cases are impossible") ))    in 
             dprint (fun () -> "**** cD'_ext = " ^ P.mctxToString cO cD'_ext);
            let cPsi'  = Whnf.cnormDCtx (cPsi', theta) in
            let spine' = Whnf.cnormSpine (spine', theta) in
            let tA'    = Whnf.cnormTyp (tA', theta) in
              (* build ground instantiated objects *) 

            let ms2 = Whnf.mcomp (Whnf.mcomp ms (LF.MShift (offset+1))) theta in 

              Debug.indent 2; dprint (fun () -> "PVars; verify, before calling app");
              verify (cs, ms2, cO, cD'_ext, cPsi'); Debug.outdent 2;
              dprint (fun () -> "pvar SigmaLast 2\n"
                        ^ "--cD'_ext = " ^ P.mctxToString cO cD'_ext ^ "\n"
                        ^ "--  cPsi' = " ^ P.dctxToString cO cD'_ext cPsi' ^ "\n"
                        ^ "--    tA' = " ^ P.typToString cO cD'_ext cPsi' (tA', idSub) 
			^ "\n"
                        ^ "--         P = " 
			^ P.typToString cO cD'_ext cPsi' (LF.Atom(loc, a, spine'), idSub));
              Debug.indent 2;
              app (strategy, cs, ms2, cO, cD'_ext, cPsi')
                  (Whnf.cnormHead (head,theta), LF.Nil, tA')   
                  (LF.Atom(loc, a, spine'))
                  (fun arg1 arg2 arg3 -> Debug.outdent 2;
                                         k arg1 arg2 arg3)
          )
	else ()
       )
        | LF.SigmaElem _ ->
          begin
          let callAppOnComponent ((tA,s), index) =
            let tA' = Whnf.normTyp (tA, s) in
              dprint (fun () -> "pvar SigmaElem: tA = " ^ P.typToString cO cD_ext cPsi' (tA', idSub));
            let name = new_parameter_name "p@" in
            let _ = dprint (fun () -> "SigmaElem: created parameter \"" ^ R.render_name name ^ "\"") in
            let pdecl    = LF.PDecl(name, Whnf.normTyp(LF.Sigma typRec, id_psi), cvar_psi) in
            let cD_ext_pdecl = LF.Dec(cD_ext, pdecl) in

            let cPsi' = Whnf.cnormDCtx (cPsi', LF.MShift 1) in
              dprint (fun () -> "    tA' = " ^ P.typToString cO cD_ext_pdecl cPsi' (tA', idSub));
            let spine' = Whnf.cnormSpine (spine, LF.MShift (offset + 1)) in
              (*   cO ; cD_ext, pdecl  |- cPsi' dctx
		   cO ; cD_ext, pdecl ; cPsi' |- tA'     : type
		   cO ; cD_ext, pdecl ; cPsi' |- a spine : type
              *)
            let msub_ref  = Ctxsub.mctxToMSub cD_ext_pdecl in                
	      dprint (fun () -> "Created msub_ref : " ^ P.msubToString cO LF.Empty msub_ref);
	      dprint (fun () -> " cD_ext_pdecl : " ^ P.mctxToString cO cD_ext_pdecl );
            let cPsi_inst  = Whnf.cnormDCtx (cPsi', msub_ref) in 
	      dprint (fun () -> "cPsi_inst = " ^ P.dctxToString cO LF.Empty cPsi_inst);
            let unifyLeft = Whnf.cnormTyp (LF.Atom(loc, a, spine'), msub_ref) in
              dprint (fun () -> "    unifyLeft = Atom(_, a, spine') = " );
	      dprint (fun () -> P.typToString cO LF.Empty cPsi_inst (unifyLeft, idSub));
	      dprint (fun () -> "   tA' = "); 
     	      dprint (fun () -> P.typToString cO cD_ext_pdecl cPsi' (tA', idSub));
            let unifyRight = Whnf.cnormTyp (tA', msub_ref) in
	      dprint (fun () -> "   unifyRight = tA' = "); 
     	      dprint (fun () -> P.typToString cO LF.Empty cPsi_inst (unifyRight, idSub));
            
              if (try
                   U.unifyTyp LF.Empty cPsi_inst (unifyLeft, idSub) (unifyRight, idSub);
                   true
		  with U.Unify s ->
                    begin
                      dprnt "callOnComponent: types didn't unify; this component impossible";
                      false
                    end
		 )
              then begin
                let (theta, cD'_ext) = (try Abstract.abstractMSub (Whnf.cnormMSub msub_ref)  
					with Abstract.Error s -> 
					  raise (NoCover (fun () -> "Abstraction failed: " ^ s ^ 
							    "\n This indicates that generated patterns contained unification-problems outside the decidable pattern fragment; \n there are two solutions: try setting the coverage depth higher or prove by hand that some cases are impossible") )
				       )
		in 
                  dprint (fun () -> "**** cD'_ext = " ^ P.mctxToString cO cD'_ext);
                (* let cD'_ext = Whnf.normMCtx cD'_ext in *)
		let cPsi'  = Whnf.cnormDCtx (cPsi', theta) in
		let spine' = Whnf.cnormSpine (spine', theta) in
		let tA'    = Whnf.cnormTyp (tA', theta) in
		  (* build ground instantiated objects *) 

		let ms2 = Whnf.mcomp (Whnf.mcomp ms (LF.MShift (offset+1))) theta in 
                let h   = Whnf.cnormHead (head, theta) in 
		let sA1 = LF.getType head (typRec, idSub) 1 1 in
		let sA2 = LF.getType head (typRec, idSub) 2 1 in
                  dprint (fun () -> "pvar SigmaElem 1 (index = " ^ string_of_int index ^ ")\n"
		    ^ "cPsi' " ^ P.dctxToString cO cD'_ext cPsi' ^ "\n"
                    ^ "head = " ^ P.headToString cO cD'_ext cPsi' h ^ "\n"
                    ^ "typRec = " ^ P.typRecToString cO cD'_ext cPsi' (typRec, idSub) ^ "\n"
		    ^ "tA1 = " ^ P.typToString cO cD'_ext cPsi' sA1 ^ "\n"
		    ^ "tA2 = " ^ P.typToString cO cD'_ext cPsi' sA2 ^ "\n"
                    ^ "tA' = " ^ P.typToString cO cD'_ext cPsi' (tA', idSub) ^ "\n"
                    ^ " P = " ^ P.typToString cO cD'_ext cPsi (LF.Atom(loc, a, spine'), idSub));
		  
                  dprint (fun () -> "pvar SigmaElem 2a\n"
                                      ^ "--cD'_ext = " ^ P.mctxToString cO cD'_ext ^ "\n");
                  dprnt "tA' OK (1)";
                Lfcheck.checkTyp cO cD'_ext cPsi' (tA', idSub);
                dprnt "tA' OK (2)";
                Lfcheck.checkTyp cO cD'_ext cPsi' (LF.Atom(loc, a, spine'), idSub);
                dprnt "P OK";
                Debug.indent 2;
                app (strategy, cs, ms2, cO, cD'_ext, cPsi')
                  (LF.Proj(h, index), LF.Nil, tA')
                  (LF.Atom(loc, a, spine'))
                  (fun arg1 arg2 arg3 ->
                     Debug.outdent 2;
                     k arg1 arg2 arg3)
              end else ()
          in
            iterTypRec callAppOnComponent (head, (Whnf.cnormTypRec (typRec, LF.MShift 1) , id_psi))
          end

  
  and callAppOnConcrete (LF.BVar x, xTyp) =
    dprint (fun () -> "checking if bound variable \"" ^ 
	      R.render_bvar cPsi x ^ "\" is covered");
    dprint (fun () -> "--the variable's type is: " ^ P.typToString cO cD cPsi (xTyp, idSub));
    app (strategy, cs, ms, cO, cD, cPsi)
      (LF.BVar x, LF.Nil, xTyp)
      (LF.Atom(loc, a, spine))
      k


  and callAppOnConstructor (c, cSig) =
    dprint (fun () -> "checking if constructor \"" ^ 
	      R.render_cid_term c ^ "\" is covered");
    dprint (fun () -> "--type cSig: " ^ P.typToString cO cD cPsi (cSig, idSub));
    app (strategy, cs, ms, cO, cD, cPsi)
      (LF.Const c, LF.Nil, cSig)
      (LF.Atom(loc, a, spine))
      k
  in
    List.iter callAppOnConstructor constructorsWithTypes;
    List.iter callAppOnPVar sch_elems;
    List.iter callAppOnConcrete concretesWithTypes


(*
 * Obj-no-split / "MVars" rule
 *
 * cO |- cs : cO'  and cO ; cD |- ms : cD'
 *
 * cO ; cD ; cPsi |- a spine : type
 *
 *)
and obj_no_split (strategy, cs, ms, cO, cD, cPsi) (loc, a, spine) k =
  dprnt "obj_no_split";
   Debug.indent 2;
   verify (cs, ms, cO, cD, cPsi);
   let tP = LF.Atom(loc, a, spine) in
   let (flat_cPsi, conv_list) = ConvSigma.flattenDCtx cPsi in  
   let s_proj = ConvSigma.gen_conv_sub conv_list in
   let tP'    = ConvSigma.strans_typ (tP, Substitution.LF.id) conv_list in

   dprint (fun () -> "before thin: " ^ P.dctxToString cO cD flat_cPsi);

   (* this is wrong here ... -bp 
      Example: flat_cPsi = g, T1 : i
               thin_cPsi = T1:i

      then thin_sub should be : 1. CtxShift(g)+1   
         and not CtxShift(g) + 0
   *)
   let (thin_sub, thin_cPsi) = Subord.thin (cO, cD) (tP', flat_cPsi) in

   (* flat_cPsi |- thin_sub : thin_cPsi *)
   (* flat_cPsi |- tP' type              *)
   let inv_thin_sub = Substitution.LF.invert thin_sub in 
   dprint (fun () -> "s_proj: " ^ P.subToString cO cD cPsi s_proj);
   dprint (fun () -> "thin-subst.: \n      " ^ 
	     P.dctxToString cO cD flat_cPsi ^ "   |-   \n        " ^ 
	     P.subToString cO cD flat_cPsi thin_sub ^ "   : " ^ 
	  P.dctxToString cO cD thin_cPsi);
   dprint (fun () -> "tP:          " ^ P.typToString cO cD cPsi (tP, idSub));
   let tP_thinned = Whnf.normTyp (tP', inv_thin_sub) in 
   let name = new_name "NOSPLIT" in
   dprint (fun () -> "new MVar " ^ R.render_name name ^ " has type  " 
	     ^ P.typToString cO cD thin_cPsi (tP_thinned, Substitution.LF.id)
             ^ "  in thinned context [" ^ P.dctxToString cO cD thin_cPsi ^ "]\n");
   let decl  = LF.MDecl(name, tP_thinned, thin_cPsi) in 
   dprint (fun () -> "thin_sub o s_proj = " ^ 
	     P.subToString cO cD cPsi (Substitution.LF.comp thin_sub s_proj));

   dprint (fun () -> "obj_no_split -- verify ...thin_cPsi");
   verify (cs, ms, cO, cD, thin_cPsi);
   dprint (fun () -> "obj_no_split -- verified ...thin_cPsi\n");

   let cD'       = LF.Dec(cD, decl) in
   let target_tP = Whnf.cnormTyp(tP, LF.MShift 1) in 
   let cPsi'     = Whnf.cnormDCtx (cPsi, LF.MShift 1) in
   (* cD' ; cPsi' |- target_tP : type *)
   
   let h : LF.head = LF.MVar(LF.Offset 1, Substitution.LF.comp thin_sub s_proj)  in

   dprint (fun () -> "\nobj_no_split -- verify cD' |- cPsi'");
   verify (cs, Whnf.mcomp ms (LF.MShift 1), cO, cD', cPsi');

   let tR1 = LF.Root(loc, h, LF.Nil) in

   dprint (fun () -> "obj_no_split:\n"
                   ^ "--cD; = " ^ P.mctxToString cO cD');
   dprint (fun () -> "–-cPsi' = " ^ P.dctxToString cO cD' cPsi' );
   dprint (fun () -> "--tR1 (instance) = " ^ P.normalToString cO cD' cPsi' (tR1, idSub));
   dprint (fun () -> "--target_tP = " ^ P.typToString cO cD' cPsi' (target_tP, idSub));
   Debug.outdent 2;
   k (strategy, cs, Whnf.mcomp ms (LF.MShift 1), cO, cD', cPsi')
     tR1
     target_tP  (* tP*)



(*
 * Obj-Pi; Obj-Sigma; call to Obj-split/Obj-no-split
 *)
and obj (strategy, cs, ms, cO, cD, cPsi) tA k =
  dprint (fun () -> "obj: " ^ "\n"
	          ^ "in cPsi = " ^ P.dctxToString cO cD cPsi 
                  ^ "\n --tA: " ^ P.typToString cO cD cPsi (tA, idSub));
  verify (cs, ms, cO, cD, cPsi);
  match tA with
  | LF.PiTyp ((LF.TypDecl(name, tA1) as typdecl, depend), tA2) ->   (* rule Obj-Pi *)
     dprint (fun () -> "PiTyp");
     Debug.indent 2;
     (let extended_cPsi = LF.DDec(cPsi, typdecl) in
       obj (strategy, cs, idMSub, cO, cD, extended_cPsi)
         tA2
         (fun (strategy, cs', ms', cO, cD, _extended_cPsi) tM tA2 ->
            let cPsi = Whnf.cnormDCtx (cPsi, ms') in
            let tA1 =  Whnf.cnormTyp  (tA1, ms') in
            let typdecl = LF.TypDecl(name, tA1) in
              k (strategy, cs', Whnf.mcomp ms ms', cO, cD, cPsi)
                (LF.Lam (None, name, tM))
                (LF.PiTyp ((typdecl, depend), tA2)))
     );
     Debug.outdent 2

  | LF.Sigma _typ_rec ->  (* rule Obj-Sigma *)
      dprint (fun () -> "coverage.ml obj Sigma case...exiting");
      exit 222

  | LF.Atom (loc, a, spine) ->    (* rule Obj-split *)
     (* cO ; cD ; cPsi |- tA  
	cO  |- cs : cO'   and  cO ; cD |- ms : cD'
      *)
     split_switch strategy
       (begin (* Split *)
          fun strategy ->	     
	     dprint (fun () -> "Calling obj_split:\n -- Trapping cPsi = " ^ 
		       P.dctxToString cO cD cPsi);
	     dprint (fun () -> "--      a: " ^ R.render_cid_typ a);
	     dprint (fun () -> "--  spine: " ^ 
		       P.spineToString cO cD cPsi (spine, idSub));

             obj_split (strategy, cs, idMSub, cO, cD, cPsi) (loc, a, spine)
               (fun (strategy', cs', ms', cO, cD, cPsi) b c ->   
		  (* Restore the previous strategy, including strategy.currDepth *)
                  verify (cs', Whnf.mcomp ms ms', cO, cD, cPsi);
                  k (strategy, cs', Whnf.mcomp ms ms', cO, cD, cPsi) b c)
          end, begin
           (* Don't split *)
           fun strategy ->
             obj_no_split (strategy, cs, ms, cO, cD, cPsi) (loc, a, spine) k
         end)


let rec contextDep_split (strategy, cs, ms, cO, cD, cPsi) k =
  let continue (strategy, cs, ms, cO, cD, cPsi) k =
        k (increment_context_depth strategy, cs, ms, cO, cD, cPsi) in
  match cPsi with
  | LF.Null -> continue (strategy, cs, ms, cO, cD, cPsi) k
  | LF.CtxVar _ -> continue (strategy, cs, ms, cO, cD, cPsi) k
  | LF.DDec (cPsi', LF.TypDecl (name, tConcrete)) ->
    begin match tConcrete with
    | LF.Atom (loc, a, spine) ->
    (*                let hung_cPsi' = hangDCtx shift cPsi' in *)
      let a_kind = (Types.get a).Types.kind in

      let rec objSpine (strategy, cs, ms2, cO, cD, cPsi') outSpine (inSpine, typ) k =
        match (inSpine, typ) with
        | (LF.Nil,  LF.Atom (_loc, _b, _tSpine)) ->
          k (strategy, cs, ms2, cO, cD, cPsi') outSpine
        | (LF.App(tM, inTail),  LF.PiTyp((LF.TypDecl(_, type_of_tM), _depend), rightTyp)) ->
          let pass () = objSpine (strategy, cs, ms2, cO, cD, cPsi') 
	                         (LF.App(tM, outSpine)) (inTail, rightTyp) k in
          (* let inTail = hangSpine shift inTail in
             let outSpine = hangSpine shift outSpine in
             let rightTyp = hangTyp shift rightTyp in *)
          begin match tM with
          | LF.Lam (_loc, _name, _body)    -> (* possible -- fix (also below) *)   pass()
          | LF.Root (_loc, LF.BVar _, _)   -> (* can't split *)  pass()
          | LF.Root (_loc, LF.PVar _, _)   -> (* can't split *)  pass()
          | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible *)   pass()
          | LF.Root (_loc, LF.Proj _, _)   -> (* can't split *)  pass()
          | LF.Root (loc, LF.Const c, innerSpine) ->
              objSpine (strategy, cs, idMSub, cO, cD, cPsi') LF.Nil 
		(innerSpine, (Constructors.get c).Constructors.typ)
                (fun (strategy, cs, ms'2, cO, cD, cPsi') newInnerSpine ->
                   let ms3 = Whnf.mcomp ms2 ms'2 in
                     verify (cs, ms3, cO, cD, cPsi');
                   let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                   let inTail = sSpine inTail ms'2 in
                   let outSpine = sSpine outSpine ms'2 in
                   let outSpine = appendToSpine outSpine newRoot in
                   let rightTyp = sTyp rightTyp ms'2 in
                     objSpine (strategy, cs, ms3, cO, cD, cPsi') outSpine (inTail, rightTyp) k)
	  | LF.Root (loc, LF.MVar _, _) ->
            let originalPhase = strategy.phase in
            let strategy = {strategy with phase = TermPhase} in                        
              obj (strategy, cs, idMSub, cO, cD, cPsi') type_of_tM
                (fun (strategy, cs, ms'2, cO, cD, _cPsi') splitM _typeOfSplitM ->
                   let ms3 = Whnf.mcomp ms2 ms'2 in
                   let strategy = {strategy with phase = originalPhase} in
                   let inTail = sSpine inTail ms'2 in
                   let outSpine = sSpine outSpine ms'2 in
                   let outSpine = appendToSpine outSpine splitM in
                   let rightTyp = sTyp rightTyp ms'2 in
                     objSpine (strategy, cs, ms3, cO, cD, cPsi') outSpine (inTail, rightTyp) k)
          end
                
      and objSpineKind (strategy, cs, ms2, cO, cD, cPsi') outSpine (inSpine, kind) k =
        match (inSpine, kind) with
          | (LF.Nil,  LF.Typ)  ->  k (strategy, cs, ms2, cO, cD, cPsi') outSpine
          | (LF.App(tM, inTail),  LF.PiKind((LF.TypDecl(_, type_of_tM), _depend), rightKind))  ->
              let pass () = objSpineKind (strategy, cs, ms2, cO, cD, cPsi') 
		              (LF.App(tM, outSpine)) (inTail, rightKind) k in
	   (* let inTail = hangSpine shift inTail in
              let outSpine = hangSpine shift outSpine in *)
              begin match tM with
              | LF.Lam (_loc, _name, _body)    -> (* possible -- fix (also above) *)   pass()
              | LF.Root (_loc, LF.BVar _, _)   -> (* can't split *)  pass()
              | LF.Root (_loc, LF.PVar _, _)   -> (* can't split *)  pass()
              | LF.Root (_loc, LF.AnnH _, _)   -> (* impossible *)   pass()
              | LF.Root (_loc, LF.Proj _, _)   -> (* can't split *)  pass()
              | LF.Root (loc, LF.Const c, innerSpine) ->
                  objSpine (strategy, cs, idMSub, cO, cD, cPsi') LF.Nil 
		    (innerSpine, (Constructors.get c).Constructors.typ)
                    (fun (strategy, cs, ms'2, cO, cD, cPsi') newInnerSpine ->
                       let ms3 = Whnf.mcomp ms2 ms'2 in
                         verify (cs, ms3, cO, cD, cPsi');
                       let newRoot = LF.Root (loc, LF.Const c, newInnerSpine)  in
                       let inTail = sSpine inTail ms'2 in
                       let outSpine = sSpine outSpine ms'2 in
                       let outSpine = appendToSpine outSpine newRoot in
                         objSpineKind (strategy, cs, ms3, cO, cD, cPsi') outSpine 
			   (inTail, rightKind) k)

              | LF.Root (loc, LF.MVar (_, mvarsub), _) ->
                  dprint (fun () -> "CRITICAL POINT: incoming cPsi' is [" ^ 
			    P.dctxToString cO cD cPsi' ^ "];\n"
                            ^ "                mvarsub is  " ^ 
			    P.subToString cO cD cPsi' mvarsub);
                  let originalPhase = strategy.phase in
                  let strategy = {strategy with phase = TermPhase} in (* splitting depth off? *)
                    obj (strategy, cs, idMSub, cO, cD, cPsi') type_of_tM
                      (fun (strategy, cs, ms'2, cO, cD, cPsi') splitM _typeOfSplitM ->
                         let ms3 = Whnf.mcomp ms2 ms'2 in
                         let strategy = {strategy with phase = originalPhase} in
                         let inTail = sSpine inTail ms'2 in
                         let outSpine = sSpine outSpine ms'2 in
                         let outSpine = appendToSpine outSpine splitM in
                           objSpineKind (strategy, cs, ms3, cO, cD, cPsi') outSpine 
			     (inTail, rightKind) k)
              end
      in
        objSpineKind (strategy, cs, idMSub, cO, cD, cPsi') LF.Nil (spine, a_kind)
          (fun (strategy, cs', ms', cO, cD, _cPsi') splitSpine ->
             let cPsi' = sDCtx cPsi' ms' in
               contextDep (strategy, cs, Whnf.mcomp ms ms', cO, cD, cPsi')
                 (fun (strategy, cs, ms'', cO, cD, new_cPsi') ->
                    verify (cs, ms'', cO, cD, new_cPsi');
                    let splitTypDecl = LF.TypDecl (name, LF.Atom (loc, a, splitSpine)) in
                    let reconstitutedPsi = LF.DDec (new_cPsi', splitTypDecl) in
                      dprint (fun () -> "* splitTypDecl in \"" ^ R.render_name name ^ "\": "
                                ^ P.dctxToString cO cD reconstitutedPsi ^ " |- " ^ "___ " 
				^ P.spineToString cO cD reconstitutedPsi (splitSpine, idSub));
                      verify (cs, ms'', cO, cD, reconstitutedPsi);
                      dprnt "done...";
                      continue (strategy, cs, ms'', cO, cD, reconstitutedPsi) k))
	  
    | whatever ->
        contextDep (strategy, cs, idMSub, cO, cD, cPsi')
          (fun (strategy, cs, ms', cO, cD, new_cPsi') ->
             verify (cs, Whnf.mcomp ms ms', cO, cD, new_cPsi');
             let tConcrete = sTyp tConcrete ms' in
               continue (strategy, cs, Whnf.mcomp ms ms', 
			 cO, cD, LF.DDec (new_cPsi', LF.TypDecl (name, tConcrete))) k)
    end


and contextDep (strategy, cs, ms, cO, cD, cPsi) k =
    Debug.indent 2;
    contextDep_split_switch strategy
      (begin (* Split *)
       fun strategy -> 
         contextDep_split (strategy, cs, ms, cO, cD, cPsi)
           (fun (strategy', cs, ms, cO, cD, cPsi) ->
               verify (cs, ms, cO, cD, cPsi);
               Debug.outdent 2;
               (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, cs, ms, cO, cD, cPsi))
        end, begin
         (* Don't split *)
         fun strategy ->
           Debug.outdent 2;
           verify (cs, ms, cO, cD, cPsi);
           k (strategy, cs, ms, cO, cD, cPsi)
      end)

(* context_split (strategy, cs, ms, cO, cD, cPsi) k = ()

   cO |- cs : cO'
   cO ; cD |- ms : cD'
   cO ; cD |- cPsi : dctx

    Split the context variable in cPsi

*)
let rec context_split (strategy, cs, ms, cO, cD, cPsi) k =
  let strategy = increment_context_variable_depth strategy in
  (* If cPsi = g, cConcrete where g's schema is (tA1 + tA2 + ...) then:
     Call `context' with cPsi := g, _:tA1, cConcrete
     then with cPsi := g, _:tA2, cConcrete
     etc.
  *)

  (* replace (cPsi_refined, psi_i) cPsi = (cPsi' , cs)
    
     if cO = psi1, .. psin
     s.t. [psi1, cPsi_refined/psi_i, .. psin] cPsi = cPsi' 
           [psi1, cPsi_refined/psi_i .. psin] = cs
  *)
  let replace (cPsi_refined, psi) cPsi =
    let LF.CtxOffset psi_offset = psi in 
    let (_cO, csub) = Ctxsub.inst_csub cPsi_refined psi_offset 
                                        (Ctxsub.id_csub cO) cO in
      (Ctxsub.ctxnorm_dctx (cPsi, csub), csub)
  in
  (* if cO ; cD' |- cD mctx       l = |cD|
        cO ; cD' |- cPsi_refined dctx  
     then cO ; cD' |- [cPsi_refined/psi]cD mctx
  *)
  let rec apply_ctxsub cO cD (cPsi_refined, psi) l = match cD with
    | LF.Empty -> LF.Empty
    | LF.Dec(cD', LF.MDecl(u, tA, cPhi)) -> 
	let LF.CtxOffset psi_offset = psi in 
	let (_cO, csub) = Ctxsub.inst_csub (Whnf.cnormDCtx (cPsi_refined, LF.MShift (l-1)))
	                                   psi_offset  (Ctxsub.id_csub cO) cO in
	let tA'   = Ctxsub.ctxnorm_typ (tA, csub) in
	let cPhi' = Ctxsub.ctxnorm_dctx (cPhi, csub) in
	let cD''  = apply_ctxsub cO cD' (cPsi_refined, psi) (l-1) in 
	  LF.Dec (cD'', LF.MDecl (u, tA', cPhi')) 
    | LF.Dec(cD', LF.PDecl(u, tA, cPhi)) -> 
	let LF.CtxOffset psi_offset = psi in 
	let (_cO, csub) = Ctxsub.inst_csub (Whnf.cnormDCtx (cPsi_refined, LF.MShift (l-1)))
	                                   psi_offset  (Ctxsub.id_csub cO) cO in
	let tA'   = Ctxsub.ctxnorm_typ (tA, csub) in
	let cPhi' = Ctxsub.ctxnorm_dctx (cPhi, csub) in
	let cD''  = apply_ctxsub cO cD' (cPsi_refined, psi) (l-1) in 
	  LF.Dec (cD'', LF.PDecl (u, tA', cPhi')) 

  in  
  let check psi (LF.SchElem(some_part_ctx, schema_rec)) = 
    let cPsi_just_psi = LF.CtxVar psi in
    let dctx = Context.projectCtxIntoDctx some_part_ctx in
    let (cD_ext, dctxSub, offset) = Ctxsub.ctxToSub_mclosed (LF.Empty) cPsi_just_psi dctx in    
      (*  where k = |cD_ext *)
      (* cD_ext ; cPsi_just_psi |- dctxSub' : dctx *)
    let l = Context.length cD in 
    (* let dctxSub = Whnf.cnormSub (dctxSub', LF.MShift l) in *)
      (* cD_ext ; psi |- dctxSub : dctx *)
    let schema_rec = Whnf.normTypRec (schema_rec, dctxSub) in
    let tA = match schema_rec with LF.SigmaLast tB -> tB
                                 | typ_rec -> LF.Sigma typ_rec in 
    let name = new_name "ctxvarsplit" in
    let new_decl = LF.TypDecl(name, tA) in
    let _ = dprint (fun () -> "context_split: new concrete declaration "
                            ^ R.render_name name ^ " : " 
		            ^ P.typToString cO cD_ext cPsi (tA, idSub)) in

    let cPsi_split = LF.DDec (LF.CtxVar psi, new_decl) in
    let cPsi_split' = Whnf.cnormDCtx (cPsi_split, LF.MShift l) in 
    let (cPsi', cs_split) = replace (cPsi_split', psi) cPsi in        

    let cD'     = apply_ctxsub cO cD (cPsi_split, psi) l in 
    let cD'_ext = Context.append cD_ext cD' in 
    let ms_ext  = Whnf.mvar_dot (LF.MShift offset) cD in 
    let ms'     = Whnf.mcomp ms ms_ext in 
    let _ = dprint (fun () -> "ms = " ^ P.msubToString cO cD' ms ) in 
    let _ = dprint (fun () -> "cD'_ext = " ^ P.mctxToString cO cD'_ext ) in 
    let _ = dprint (fun () -> "ms_ext = " ^ P.msubToString cO cD'_ext ms') in 

      context (strategy, (Ctxsub.ccomp cs cs_split), ms', cO, cD'_ext, cPsi') k    
  in
  let split sch_elems = match sch_elems with
    | [] ->
        context (strategy, cs, ms, cO, cD, cPsi) k
    | elems ->
        let Some psi = Context.ctxVar cPsi in
	let _ = List.iter (check psi) elems in 
	let (cPsi', cs_split) = replace (LF.Null, psi) cPsi in   
	let cD' = Ctxsub.ctxnorm_mctx (cD, cs_split) in  
	let _ = dprint (fun () -> "cD' = " ^ P.mctxToString cO cD') in 
          context (strategy, Ctxsub.ccomp cs cs_split, ms, LF.Empty , cD', cPsi') k
  in
    split (getSchemaElems cO cPsi) 


(*    context (strategy, cs, ms, cO, cD, cPsi) k = ()

      cO |- cs : cO'
      cO ; cD |- ms : cD' 
      cO ; cD |- cPsi dctx 


     Two possible kinds of splits:
      1) split a context variable (contex_split)
      2) split a dependent argument in context
*)
and context (strategy, cs, ms, cO, cD, cPsi) k =
   (Debug.indent 2;
    context_split_switch strategy
       (begin
         (* Split *)
         fun strategy -> 
          context_split (strategy, cs, ms, cO, cD, cPsi)
            (fun (strategy', cs, ms, cO, cD, cPsi) ->   
	       (* Restore the previous strategy, including strategy.currDepth *)
               k (strategy, cs, ms, cO, cD, cPsi))
        end, begin
         (* Don't split *)
         fun strategy ->
           dprint (fun () -> "strategy.phase := ContextDependentArgumentsPhase");
           let strategy = {strategy with phase = ContextDependentArgumentsPhase} in
             contextDep (strategy, cs, ms, cO, cD, cPsi) k
       end);
    Debug.outdent 2)


(*
 * covered_by  BranchBox(cO_i, cD_i, (cPsi_i, tR_i, ms_i, cs_i), _body) 
 *             (cO, cD, cPsi) tM tA
 *
 * Succeeds iff the term   cO ; cD   ; cPsi   |- tM   is covered by   
                         cO_i ; cD_i ; cPsi_i |- tR_i


   Typing Assumptions:

   branches = cO_i ; cD_i ; cPsi_i |- tM_i  
              cO_i ; cD_i  |- (cs_i , ms_i ) : (cO_orig ; cD_orig)

   cO ; cD |- cs ; ms : cO_orig  ; cD_orig

   cO ; cD ; cPsi |- tM : tA 

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
				(* NOTE: mathLeft and matchRight do not necessarily have
				   the same type, according to the specificed typing
				   invariants. *)
                                U.matchTerm matchD matchPsi matchLeft matchRight);
        
        dprint (fun () -> "MATCHED");
        Debug.outdent 2
      with U.Unify s -> (dprnt "no match";
                         Debug.outdent 2;
                         raise (NoCover (fun () -> "---inner NoCover escaped---")))


(* covered_by_set branches (strategy, cs, ms, cO, cD, cPsi) tM tA 

   Assumptions:

   branches = cO_i ; cD_i ; cPsi_i |- tM_i  
              cO_i ; cD_i  |- (cs_i , ms_i ) : (cO_orig ; cD_orig)

   cO ; cD |- cs ; ms : cO_orig  ; cD_orig

   cO ; cD ; cPsi |- tM : tA 


*)
let rec covered_by_set branches (strategy, cs, ms, cO, cD, cPsi) tM tA =
  verify (cs, ms, cO, cD, cPsi);
  match branches with
  | [] -> raise (NoCover (fun () -> "Not covered: "
                                  ^ "[" ^ P.dctxToString cO cD cPsi ^ "]  "
                                  ^ P.normalToString cO cD cPsi (tM, idSub)))
  | branch :: branches ->
    (try covered_by branch (cO, cD, cPsi) tM tA;
      dprint (fun () -> "Term covered:  " ^ P.normalToString cO cD cPsi (tM, idSub)
        ^ "  covered by  "
       ^ match branch 
         with BranchBox (cO', cD', (cPsi', NormalPattern (tR', _body), _msub', _csub')) ->
            P.normalToString cO' cD' cPsi' (tR', idSub))
      with 
        NoCover _ -> covered_by_set branches (strategy, cs, ms, cO, cD, cPsi) tM tA
    )


let rec maxSpine f = function
  | LF.Nil -> 0
  | LF.App(tM, spine) ->
      let depth_tM = f tM in
        max depth_tM (maxSpine f spine)

let rec maxTuple f = function
  | LF.Last tM -> f tM
  | LF.Cons(tM, tuple) -> max (f tM) (maxTuple f tuple)

and depth = function
  | LF.Lam(_, _, tM) -> (*1 +*) depth tM   (* should probably just be   depth tM   -jd *)
  | LF.Root(_, head, spine) -> (*1 +*) (depthHead head) + (maxSpine depth spine)
(*  | LF.Clo(tM, _) -> depth tM *)
  | LF.Tuple(_, tuple) -> (*1 +*) maxTuple depth tuple

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
  | LF.Atom(_loc, _a, spine) -> 1 + maxSpine depth spine
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
      (dprint (fun () -> "depth of EmptyPattern = 1");
       1)
  
  | BranchBox (cO', cD', (cPsi', NormalPattern (tM', _body), _msub', _csub')) ->
      let d = depth tM' in
      (dprint (fun () -> "depth of NormalPattern " ^ P.normalToString cO' cD' cPsi' (tM', Substitution.LF.id)
                       ^ " = " ^ string_of_int (1 + d));
       d)

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


(* covers : problem -> unit
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



(* covers problem = ()

  problem  = {loc: loc ; prag : pragma ; 
              cO : LF.mctx ; cD : LF.mctx ;
              branches ; domain : tA[cPsi] }

  where   cO ; cD ; cPsi |- tA  
  
*)
let covers problem =
if not (!enableCoverage) 
  then Success
else
  let (tA, cPsi) = problem.domain in
  let _ = (dprint (fun () -> "[covers] cPsi = " ^ 
		     P.dctxToString problem.cO problem.cD cPsi);
	   dprint (fun () -> "           tA = " ^ 
		     P.typToString problem.cO problem.cD cPsi (tA,idSub) )) in   
  let _ = (covby_counter := 0; Debug.pushIndentationLevel(); Debug.indent 2) in 
  let cutoff = max 1 (maxDepth problem.branches + 1 + !extraDepth) in
  let variableDepth = maxContextVariableDepth cPsi problem.branches in
  let dep = maxDependentDepth problem.branches  in
  let _ = dprint (fun () -> "cutoff depth                = " ^ string_of_int cutoff) in
  let _ = dprint (fun () -> "max context variable depth  = " ^ string_of_int variableDepth) in
  let _ = dprint (fun () -> "max dependent depth         = " ^ string_of_int dep) in
  let strategies = tabulate cutoff (fun depth -> new_strategy (depth, variableDepth, dep)) in
  try
    dprint (fun () -> "Coverage checking a case with "
              ^ string_of_int (List.length problem.branches)  
	      ^ " branch(es) at:\n"
              ^ Pretty.locOptToString problem.loc);
    tryList
      (fun strategy ->
         Debug.pushIndentationLevel();
         dprint (fun () -> "trying strategy " ^ strategyToString strategy);
         begin try
           context (strategy, idCSub, idMSub, problem.cO, problem.cD, cPsi)
             (fun (strategy, cs', ms', cO', cD', cPsi') ->
                (* cO' |- cs' : problem.cO
                   cO' ; cD' |- ms' : [cs']problem.cD  *)
                let _ = (dprint (fun () -> "new context generated cPsi' = " 
				   ^ P.dctxToString cO' cD' cPsi') ;
			 dprint (fun () -> "cD' = " ^ P.mctxToString cO' cD' )) in
                let tA' = Ctxsub.ctxnorm_typ ((sTyp tA ms'), cs') in
		let _  = dprint (fun () -> "tA' = " ^ 
				   P.typToString cO' cD' cPsi' (tA', idSub) )  in
                let _  = dprint (fun () -> "strategy.phase := " ^ 
				   "ContextDependentArgumentsPhase") in
                let strategy = {strategy with phase = ContextDependentArgumentsPhase} in 
                  (* cO' ; cD' ; cPsi' |- tA' *)
                  contextDep (strategy, cs', ms', cO', cD', cPsi')
                    (fun (strategy, cs'', ms'', cO'', cD'', cPsi'') ->
                       (*  cO''        |- cs'' : cO' 
                           cO'' ; cD'' |- ms'' : [cs'']cD' *)
                       let _ = dprint (fun () -> "context generated cPsi'' = " ^ 
					 P.dctxToString cO'' cD'' cPsi'') in 
 		       let _ = dprint (fun () -> "cD'' = " ^ P.mctxToString cO'' cD'' ) in
		       let tA'' = Ctxsub.ctxnorm_typ ((sTyp tA ms''), cs'') in
		       let _    = dprint (fun () -> "tA'' = " 
					    ^ P.typToString cO'' cD'' cPsi'' (tA'',idSub)) in 
                       let _    = dprint (fun () -> "strategy.phase := TermPhase") in
		       let strategy = {strategy with phase = TermPhase} in
                         obj (strategy, cs'', ms'', cO'', cD'', cPsi'')
                           tA''
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
                       Printf.sprintf "\n## Case expression covers ; UNSOUNDLY(?): ##\n##   %s\n##\n\n"
                         (Pretty.locOptToString problem.loc))
      end 
    with NoCover messageFn ->
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
