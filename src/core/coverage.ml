(** Coverage checker

   @author Joshua Dunfield
*)

open Syntax.Int
open Syntax.Int.Comp

module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module U = Unify.EmptyTrail   (* is EmptyTrail the right one to use?  -jd *)
module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [15])

let covby_counter = ref 0

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


(* COPIED from opsem.ml *)
let rec cctxToCSub cO cD cPsi = match cO with
  | LF.Empty -> LF.CShift 0
  | LF.Dec (cO, LF.CDecl (_psi, schema)) -> 
      let ctxVar = LF.CtxVar (LF.CInst (ref None, schema, cO, cD)) in
      let cs = cctxToCSub cO cD cPsi in 
        LF.CDot (ctxVar, cs)

(* COPIED from opsem.ml *)
let rec mctxToMSub cD = match cD with
  | LF.Empty -> Whnf.m_id
  | LF.Dec (cD', LF.MDecl(_, tA, cPsi)) ->
      let t     = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi,t) in
      let tA'   = Whnf.cnormTyp (tA, t) in
      let u     = Whnf.newMVar (cPsi', tA') in
      let phat  = Context.dctxToHat cPsi' in
        LF.MDot (LF.MObj (phat, LF.Root (None, LF.MVar (u, Substitution.LF.id), LF.Nil)) , t)

  | LF.Dec(cD', LF.PDecl(_, tA, cPsi)) ->
      let t    = mctxToMSub cD' in
      let cPsi' = Whnf.cnormDCtx (cPsi, t) in
      let p    = Whnf.newPVar (cPsi', Whnf.cnormTyp (tA, t)) in
      let phat = Context.dctxToHat cPsi' in
        LF.MDot (LF.PObj (phat, LF.PVar (p, Substitution.LF.id)) , t)



(*
 * type shifter  ---Shifter
 *
 * Shifter passed into the continuation, to fix indices in things created
 * before Delta was extended.
 *)
type shifter = {
  head : LF.head -> LF.head;
  spine : LF.spine -> LF.spine;
  normal : LF.normal -> LF.normal;
  typ : LF.typ -> LF.typ
}

let noop_shift = {head = (fun h -> h);
                  spine = (fun s -> s);
                  normal = (fun tM -> tM);
                  typ = (fun t -> t)}

let bump_shift n shift =
  {head = (fun h -> Whnf.mshiftHead (shift.head h) n);
   spine = (fun spine -> Whnf.mshiftSpine (shift.spine spine) n);
   normal = (fun tM -> Whnf.mshiftTerm (shift.normal tM) n);
   typ = (fun t -> Whnf.mshiftTyp (shift.typ t) n)
  }

(*
 * type strategy  ---Coverage strategy
 *
 * This type represents the strategy (or the state of the strategy) to use.
 * Currently, this just has a `depth'.
 * (And the depth is, absurdly, a constant!)
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
let rec app (strategy, shift, cO, cD, cPsi) (tR, spine, tA) tP k =
  let _ = dprint (fun () -> "App: tR = " ^ P.headToString cO cD cPsi tR ^ "\n"
                          ^ "App: tA = " ^ P.typToString cO cD cPsi (tA, emptySub) ^ "\n"
                          ^ "App: tP = " ^ P.typToString cO cD cPsi (tP, emptySub)) in
  match tA with
  | LF.PiTyp (((LF.TypDecl(x, tA1)) as x_decl, _depend), tA2) ->   (* rule App-Pi *)
      let cPsi_x = LF.DDec(cPsi, x_decl) in
      let _ = dprint (fun () -> "App-Pi(0): " ^ P.typToString cO cD cPsi_x (tA2, emptySub)) in
      obj (strategy, shift, cO, cD, cPsi) tA1
        (fun (strategy, shift, cO, cD, _cPsi) tM tA1 ->
           let _ = dprint (fun () -> "App-Pi(tM): " ^ P.normalToString cO cD cPsi (tM, emptySub)) in
           let tA2 = shift.typ tA2 in
           let substitution = LF.Dot(LF.Obj ((*Context.dctxToHat cPsi,*) tM), emptySub) in
           let tA2_tM = Whnf.normTyp (tA2, substitution) in
           let _ = dprint (fun () -> "App-Pi(1): " ^ P.typToString cO cD cPsi (tA2_tM, emptySub)) in
           app (strategy,
                noop_shift (* we apply the shift to everything here,
                              so we must reset it or we'll overshift *),
                cO,
                cD,
                cPsi)
               (shift.head tR,
                appendToSpine (shift.spine spine) tM,
                tA2_tM)
               (shift.typ tP)
               k)
(*
  | LF.Sigma typ_rec ->     (* rule App-Sigma *)
*)
  | LF.Atom(loc, a, typeSpine) as tQ ->
      begin
        Debug.indent 2;
        let unifyLeft = (tQ, emptySub) in 
        let unifyRight = (tP, emptySub) in 
        dprint (fun () -> "App-??unify: " ^ P.typToString cO cD cPsi unifyLeft ^ " =?= "
                             ^ P.typToString cO cD cPsi unifyRight);
(*        let xxxUnifyTyp cD cPsi left right = match (left, right) with
              | (LF.Atom(_, _, spine1),  LF.Atom(_, _, spine2)) ->
*)                  
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

(*
  Obj-split rule (Fig. 6)
*)
and obj_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
  let _ = dprint (fun () -> "obj_split: ") in
  let _ = dprint (fun () -> "--      a: " ^ R.render_cid_typ a) in
  let _ = dprint (fun () -> "--  spine: " ^ P.spineToString cO cD cPsi (spine, emptySub)) in
  (* ... PVars premises ... *)
  (* ... App<x_1> thru App<x_k> premises ... *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in
  let callApp (c, cSig) =
        dprint (fun () -> "checking if " ^ R.render_cid_term c ^ " is covered");
        Debug.indent 2;
        dprint (fun () -> "--original type: " ^ P.typToString cO cD cPsi (cSig, emptySub));
        let (cSig, offset) = Abstract.abstrTyp cSig in
        let shift = bump_shift offset shift in
          dprint (fun () -> "--abstracted type: " ^ P.typToString cO cD cPsi (cSig, emptySub));
          app (decrement_depth strategy, shift, cO, cD, cPsi)
              (LF.Const c, LF.Nil, cSig)
              (LF.Atom(loc, a, spine))
              k;
          Debug.outdent 2
  in
    List.iter callApp constructorsWithTypes

(*
 * Obj-no-split / "MVars" rule
 *)
and obj_no_split (strategy, shift, cO, cD, cPsi) (loc, a, spine) k =
  (dprnt "obj_no_split";
   Debug.indent 2;
   let tP = LF.Atom(loc, a, spine) in
   let cPsi1 = cPsi in
   let decl  = LF.MDecl(new_name "NOSPLIT", tP, cPsi1) in
   let cDWithVar = LF.Dec(cD, decl) in
   let tR1 : LF.head = LF.MVar(LF.Offset 1, Substitution.LF.id)  in
   let tM1 = LF.Root(loc, tR1, LF.Nil) in
   let _ = dprint (fun () -> "obj_no_split: " ^ P.normalToString cO cDWithVar cPsi1 (tM1, emptySub)) in
   k (strategy, bump_shift 1 shift, cO, cDWithVar, cPsi1)
     tM1
     tP;
   Debug.outdent 2)

(*
 * Obj-Pi; Obj-Sigma; call to Obj-split/Obj-no-split
 *)
and obj (strategy, shift, cO, cD, cPsi) tA k =
  let _ = dprint (fun () -> "obj: ") in
  let _ = dprint (fun () -> "--tA: " ^ P.typToString cO cD cPsi (tA, emptySub)) in
  match tA with
(*
  | LF.PiTyp ((TypDecl(name, tA1), depend) as typdecl, tA2) ->   (* rule Obj-Pi *)
      obj cO cD (*extend cPsi *)cPsi tA2
          (fun cO cD _cPsi tM tA ->
             k cO cD cPsi (Lam(None, name, tM)) (PiTyp(typdecl, tA2)))

  | LF.Sigma typ_rec ->  (* rule Obj-Sigma *)
*)

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
      let _ = dprnt  ("covered_by") in
      let _ = Debug.indent 2 in

      let cDConjoint = Context.append cD cD' in

      let ct = cctxToCSub cO' cD' cPsi' in 
      let ct' = Ctxsub.ccomp csub' ct in
      let _ = U.unifyCSub csub' ct'  in 
      let _ct1' = Ctxsub.ctxnorm_csub ct' in
      let ct1 = Ctxsub.ctxnorm_csub ct in
      let mt = mctxToMSub (Ctxsub.ctxnorm_mctx (cD', ct1)) in 
      let tR1' = Whnf.cnorm (Ctxsub.ctxnorm (tR', ct1), mt) in
      let _mt1' = Whnf.cnormMSub mt in
      let cPsi' = Ctxsub.ctxnorm_dctx (cPsi', ct1) in

      let tR' = tR1' in

      let tM_shifted = Whnf.cnorm (tM, LF.MShift (Context.length cD'))  in
      
      let _ = dprint (fun () -> P.octxToString cO ^ " |- Pi " ^ P.mctxToString cO cD
                    ^ " box(Psihat. " ^ P.normalToString cO cDConjoint cPsi (tM_shifted, emptySub)
                    ^ ") : " ^ P.typToString cO cD cPsi (tA, emptySub)
                    ^ "["    ^ P.dctxToString cO cD cPsi ^ "]") in
      let _ = dprnt  (" COVERED-BY ") in
      let _ = dprint (fun () -> P.octxToString cO' ^ " |- Pi " ^ P.mctxToString cO' cD'
                              ^ " box(Psihat. " ^ ""
                              ^ P.normalToString cO' cDConjoint cPsi' (tR', emptySub)
                              ^ ") : " ^ P.msubToString cO' cD' msub'
                              ^ "[" ^ P.csubToString cO' cD' csub' ^ "]") in
      let matchD = cDConjoint in
      let matchPsi = cPsi in
      let matchLeft = (tM_shifted, emptySub) in
      let matchRight = (tR', emptySub) in
      try
        dprnt ("About to call matchTerm:");
        dprnt ("  matchTerm ");
        dprint (fun () -> "    D = " ^ P.mctxToString cO matchD);
        dprint (fun () -> "  Psi = " ^ P.dctxToString cO matchD matchPsi);
        dprint (fun () -> " left = " ^ P.normalToString cO matchD matchPsi matchLeft);
        dprint (fun () -> "right = " ^ P.normalToString cO matchD matchPsi matchRight);
        U.matchTerm matchD matchPsi matchLeft matchRight;
        dprint (fun () -> "MATCHED");
        Debug.outdent 2
      with U.Unify s -> (dprnt "no match";Debug.outdent 2; raise NoCover)


let rec covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA = match branches with
  | [] -> raise NoCover
  | branch :: branches ->
      try covered_by branch (cO, cD, cPsi) tM tA
      with NoCover -> covered_by_set branches (strategy, shift, cO, cD, cPsi) tM tA

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
      depth tM'

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
  Debug.outdent 2

let covers cO cD cG branches (tA, cPsi) =
  if not (!enableCoverage) then ()
  else
    begin
      covby_counter := 0;
      Debug.indent 2;
      let cutoff = maxDepth branches in
      let _ = dprint (fun () -> "cutoff depth = " ^ string_of_int cutoff) in
      let strategies = tabulate cutoff naive_strategy in
        try
          dprint (fun () -> "coverage check a case with "
                              ^ string_of_int (List.length branches) ^ " branch(es)");

          tryList
            (fun strategy -> begin
                               print_string ("trying strategy " ^ strategyToString strategy ^ "\n");
                               obj (strategy, noop_shift, cO, cD, cPsi)
                                   tA
                                   (covered_by_set branches)
                             end)
            strategies;

          dprint (fun () -> "## COVERS ##");
          finish()
        with
          NoCover -> (finish(); raise NoCover)
    end
