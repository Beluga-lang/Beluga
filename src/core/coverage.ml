open Syntax.Int
open Syntax.Int.Comp

module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module U = Unify.EmptyTrail
module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.DefaultCidRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [15])

exception NoCover

let enableCoverage = ref false

let emptySub = Substitution.LF.id (* LF.Shift (LF.NoCtxShift, 0) *)

let getConstructorsAndTypes a =
  let constructors = (Types.get a).Types.constructors in
  let constructors = List.rev constructors in
  let addType c = (c, (Constructors.get c).Constructors.typ) in
    List.map addType constructors

let rec dprintCTs cO cD cPsi = function
        | [] -> dprnt "[end of constructor list]"
        | (c, cSig) :: rest ->
             (dprnt ("\"" ^ R.render_name (Constructors.get c).Constructors.name ^ "\""
                   ^ " : " ^ P.typToString cO cD cPsi (cSig, emptySub));
              dprintCTs cO cD cPsi rest)

let rec appendToSpine spine tM = match spine with
        | LF.Nil -> LF.App(tM, LF.Nil)
        | LF.App(tM1, spine) -> LF.App(tM1, appendToSpine spine tM)

(* Rules deriving `App<R>(A > P) |> J':

   App-slashunify
   App-unify
   App-Pi
   App-Sigma *)
let rec app cO cD cPsi (tR, spine, tA) tP k = match tA with
  | LF.PiTyp ((LF.TypDecl(x, tA1), _depend), tA2) ->   (* rule App-Pi *)
      obj cO cD cPsi tA1
        (fun cO cD _cPsi tM tA1 ->
           app cO cD cPsi (tR, appendToSpine spine tM, (* [M/x] *) tA2) tP k)
(*
  | LF.Sigma typ_rec ->     (* rule App-Sigma *)
*)
  | LF.Atom(loc, a, typeSpine) as _tQ ->
      let _ = Debug.indent 2 in
      (* Assume, INCORRECTLY, that tQ and tP unify *)
      let cD' = cD in
      let theta_tR = tR in   (* WRONG *)
      let theta_tP = tP in   (* WRONG *)
      let theta_Psi = cPsi in   (* WRONG *)
        k cO cD' theta_Psi (LF.Root(loc, theta_tR, spine)) (theta_tP);
        Debug.outdent 2
        (* probably wrong: not passing theta along *)


(*
  Obj-split rule (Fig. 6)
*)
and obj_split cO cD cPsi (loc, a, spine) k =
  let _ = dprint (fun () -> "obj_split: ") in
  (* ... PVars premises ... *)
  (* ... App<x_1> thru App<x_k> premises ... *)
  let constructorsWithTypes = getConstructorsAndTypes a in
  let _ = dprnt "constructors with types: " in
  let _ = dprintCTs cO cD cPsi constructorsWithTypes in
  let callApp (c, cSig) =
        dprint (fun () -> "checking if " ^ R.render_cid_term c ^ " is covered");
        Debug.indent 2;
        app cO cD cPsi (LF.Const c, LF.Nil, cSig) (LF.Atom(loc, a, spine)) k;
        Debug.outdent 2
  in
    List.iter callApp constructorsWithTypes

and obj cO cD cPsi tA k = match tA with
(*
  | LF.PiTyp ((TypDecl(name, tA1), depend) as typdecl, tA2) ->   (* rule Obj-Pi *)
      obj cO cD (*extend cPsi *)cPsi tA2
          (fun cO cD _cPsi tM tA ->
             k cO cD cPsi (Lam(None, name, tM)) (PiTyp(typdecl, tA2)))

  | LF.Sigma typ_rec ->  (* rule Obj-Sigma *)
*)

  | LF.Atom (loc, a, spine) ->    (* rule Obj-split *)
     (Debug.indent 2;
      obj_split cO cD cPsi (loc, a, spine) k;
      Debug.outdent 2)
(* rule Obj-no-split (and the mechanism for deciding when to split) NOT YET IMPLEMENTED *)

let covered_by branch cO cD cPsi tM tA = match branch with
  | BranchBox (cO', cD', (cPsi', tR', msub', csub'), _body) ->
      (* under cO / cO' ?
         Pi cD. box(?. tM) : tA[cPsi]  =.  Pi cD'. box(?. tR') : ?[?]   *)
      let _ = dprnt  ("covered_by") in
      let _ = Debug.indent 2 in
      let _ = dprint (fun () -> P.octxToString cO ^ " |- Pi " ^ P.mctxToString cO cD
                    ^ " box(Psihat. " ^ P.normalToString cO cD cPsi (tM, emptySub)
                    ^ ") : " ^ P.typToString cO cD cPsi (tA, emptySub)
                    ^ "["    ^ P.dctxToString cO cD cPsi ^ "]") in
      let _ = dprnt  (" COVERED-BY ") in
      let _ = dprint (fun () -> P.octxToString cO' ^ " |- Pi " ^ P.mctxToString cO' cD'
                              ^ " box(Psihat. " ^ "" ^ P.normalToString cO' cD' cPsi' (tR', emptySub)
                              ^ ") : " ^ P.msubToString cO' cD' msub'
                              ^ "[" ^ P.csubToString cO' cD' csub' ^ "]") in
      let matchD = cD in
      let matchPsi = cPsi in
      let matchLeft = (tM, emptySub) in
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

let rec covered_by_set branches cO cD cPsi tM tA = match branches with
  | [] -> raise NoCover
  | branch :: branches ->
      try covered_by branch cO cD cPsi tM tA
      with NoCover -> covered_by_set branches cO cD cPsi tM tA

(* covers : Int.LF.mctx -> Int.LF.mctx -> Int.Comp.ctyp_decl LF.ctx -> Int.Comp.branch list -> (Int.LF.typ * Int.LF.dctx) -> unit
 *
 * covers cO cD cG branches (tA, cPsi)
 *   returns () if the patterns in `branches' cover all values of tA[cPsi];
 *   otherwise, raises NoCover
 *
 * Also returns () if !enableCoverage is false.
 *)
let covers cO cD cG branches (tA, cPsi) =
  if not (!enableCoverage) then ()
  else
   (Debug.indent 2;
    dprint (fun () -> "coverage check a case with "
                        ^ string_of_int (List.length branches) ^ " branch(es)");
    obj cO cD cPsi tA (covered_by_set branches);
    dprint (fun () -> "## COVERS ##");
    Debug.outdent 2)
