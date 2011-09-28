(* module Logic *)
(* author: Costin Badescu *)
module S = Substitution

open Syntax.Int


type goal =                             (* Goals            *)
  | Atom of LF.typ                      (* g ::= A          *)
  | Impl of (res * LF.typ_decl) * goal  (*     | r => g'    *)
  | All of LF.typ_decl * goal           (*     | ∀x:A. g'   *)

and res =                               (* Residual Goals   *)
  | Head of LF.typ                      (* r ::= A          *)
  | And of goal * res                   (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:A. r'   *)

type gctx = goal LF.ctx         (* cG ::= Empty | (cG', g)  *)

type query = goal * LF.sub      (* Query ::= (g, s)         *)

type clause =               (* Horn Clause ::= γ |- A :- Gs *)
    { tHead : LF.typ        (* Head A : LF.Atom             *)
    ; cVars : LF.dctx       (* Context γ : EV bound in A/Gs *)
    ; gCtx : gctx }         (* Subgoals Gs : solv. Gs => A  *)


let (dprint, dmesg) = Debug.makeFunctions (Debug.toFlags [3])

module Shift = struct

  let lR = ref 0               (* Lambda Scope Range *)

  let dR = ref 0               (* Dynamic Scope Range *)

  let dS = ref 0               (* Dynamic Shift *)

  (* 

     Invariants:
     
     Only BVars in LF.Atom's are affected.
     Substitutions are not shifted.

     i: De Bruijn index.
     k: Shifting measure.

     BV bound by λ remain invariant.
     - i < lR |- BV(i) -> BV(i)

     BV bound by a dynamic scope are shifted by dS.
     - lR < i <= dR |- BV(i) -> BV(i + dS)

     BV bound to EV are shifted by k.
     - i > lR && i > dR |- BV(i) -> BV(i + k)

  *)

  let rec shiftTyp tM k = match tM with
    | LF.Atom (l, c, tS) ->
      LF.Atom (l, c, shiftSpine tS k)
    | x -> x

  and shiftSpine tS k = match tS with
    | LF.App (tN, tS) ->
      LF.App (shiftNormal tN k, shiftSpine tS k)
    | LF.SClo (tS, s) ->
      LF.SClo (shiftSpine tS k, s)
    | LF.Nil -> LF.Nil

  and shiftNormal tN k = match tN with
    | LF.Lam (l, n, tN') ->
      begin
        ignore (incr lR) ;
        let tM = LF.Lam (l, n, shiftNormal tN' k) in
        ignore (decr lR) ; tM
      end
    | LF.Root (l, tH, tS) ->
      LF.Root (l, shiftHead tH k, shiftSpine tS k)
    | LF.Clo (tN, s) ->
      LF.Clo (shiftNormal tN k, s)
    | LF.Tuple (l, tP) ->
      LF.Tuple (l, shiftTuple tP k)
        
  and shiftHead tH k = match tH with
    | LF.BVar (i) ->
      if i > !lR && i > !dR then
        LF.BVar (i + k)
      else if i > !lR && i <= !dR then
        LF.BVar (i + !dS)
      else 
        LF.BVar (i)
    | LF.AnnH (tH, tM) ->
      LF.AnnH (shiftHead tH k, tM)
    | LF.Proj (tH, n) ->
      LF.Proj (shiftHead tH k, n)
    | x -> x

  and shiftTuple tP k = match tP with
    | LF.Last (tN) ->
      LF.Last (shiftNormal tN k)
    | LF.Cons (tN, tP') ->
      LF.Cons (shiftNormal tN k, shiftTuple tP' k)

  let shiftAtom tM (cS, dS', dR') =
    ignore (dR := dR' ; dS := dS') ; shiftTyp tM cS

end


module Convert = struct

  let rec typToClause' cPsi cG tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((typDecl, LF.Maybe), tM') ->
      typToClause' (LF.DDec (cPsi, typDecl)) cG tM' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl(_, tA), LF.No), tB) ->
      typToClause' cPsi (LF.Dec (cG, typToGoal tA (cS, dS, dR)))
        tB (cS + 1, dS, dR)
    | LF.Atom (_) as tA ->
      { tHead = (Shift.shiftAtom tA (-cS, -dS, dR))
      ; cVars = cPsi
      ; gCtx = cG }

  and typToGoal tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((typDecl, LF.Maybe), tM') ->
      All (typDecl, typToGoal tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as typDecl, LF.No), tB) ->
      Impl ((typToRes tA (cS, dS, dR), typDecl), typToGoal tB
        (cS, dS, dR + 1))
    | LF.Atom (_) as tA ->
      Atom (Shift.shiftAtom tA (-cS, -dS, dR))

  and typToRes tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((typDecl, LF.Maybe), tM') ->
      Exists (typDecl, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
      And (typToGoal tA (cS, dS, dR), typToRes tB
        (cS + 1, dS + 1, dR + 1))
    | LF.Atom (_) as tA ->
      Head (Shift.shiftAtom tA (-cS, -dS, dR))

  let rec resToClause' cPsi cG (r, s) = match r with
    | Exists (typDecl, r') ->
      resToClause' (LF.DDec (cPsi, typDecl)) cG (r', S.LF.dot1 s)
    | And (g, r') ->
      resToClause' cPsi (LF.Dec (cG, g)) (r', s)
    | Head (tA) ->
      let (tA', _) = Whnf.whnfTyp (tA, s) in
      { tHead = tA' ; cVars = cPsi ; gCtx = cG }

  let resToClause (r, s) =
    resToClause' LF.Null LF.Empty (r, s)

  let typToClause tM =
    typToClause' LF.Null LF.Empty tM (0, 0, 0)

  let rec etaExpand cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA
    in match tA with
      | LF.Atom (_) as tA ->
        let u = Whnf.newMVar (cPsi, LF.TClo (tA, s)) in
        LF.Root (None, LF.MVar (u, S.LF.id), LF.Nil)
      | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
        LF.Lam (None, x, etaExpand
          (LF.DDec (cPsi, S.LF.decSub tD s))
          (tB, S.LF.dot1 s))

  let rec dctxToSub cPsi cPhi = match cPhi with
    | LF.Null ->
      LF.Shift (LF.NoCtxShift, Context.dctxLength cPsi)
    | LF.DDec (cXi, LF.TypDecl (_, tM)) ->
      let s = dctxToSub cPsi cXi in
      let tM' = etaExpand cPsi (tM, s) in
      LF.Dot (LF.Obj tM', s)
    | LF.CtxVar (ctxVar) -> invalid_arg
      "Logic.Convert.dctxToSub': Match conflict with LF.CtxVar (_)."

  let rec dctxToSubPT cPsi cPhi s sFn = match cPhi with
    | LF.Null ->
      (s, sFn)
    | LF.DDec (cXi, LF.TypDecl (_, tM)) ->
      let (s', sFn') = dctxToSubPT cPsi cXi s sFn in
      let tM' = etaExpand cPsi (tM, s') in
      (LF.Dot (LF.Obj tM', s'), (function tS -> sFn' (LF.App (tM', tS))))
    | LF.CtxVar (ctxVar) -> invalid_arg
      "Logic.Convert.dctxToSub': Match conflict with LF.CtxVar (_)."

  let rec dctxToSub' cPsi cPhi s = match cPhi with
    | LF.Null -> s
    | LF.DDec (cXi, LF.TypDecl (_, tM)) ->
      let s' = dctxToSub' cPsi cXi s in
      let tM' = etaExpand cPsi (tM, s') in
      LF.Dot (LF.Obj tM', s')
    | LF.CtxVar (ctxVar) -> invalid_arg
      "Logic.Convert.dctxToSub': Match conflict with LF.CtxVar (_)."

  let rec typToQuery' (tM, i) s = match tM with
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.Maybe), tB) when i > 0 ->
      let tA' = etaExpand LF.Null (tA, s) in
      typToQuery' (tB, i - 1) (LF.Dot (LF.Obj tA', s))
    | _ -> (typToGoal tM (0, 0, 0), s)

  let typToQuery (tM, i) =
    typToQuery' (tM, i) S.LF.id

end


module Persist = struct

  open Store

  type entType = entClause DynArray.t

  and entClause = Id.cid_term * clause

  let tblTypes = Hashtbl.create 0

  let arrQueries = DynArray.create ()

  let addType cidTyp =
    let () = Hashtbl.add tblTypes cidTyp (DynArray.create ())
    in Hashtbl.find tblTypes cidTyp

  let addClause entType entClause =
    DynArray.add entType entClause

  let addQuery (g, s) =
    DynArray.add arrQueries (g, s)

  let lookupType cidTyp =
    Hashtbl.find tblTypes cidTyp

  let clausifyTerm cidTerm =
    let tmEntry = Cid.Term.get cidTerm in
    let tM = tmEntry.Cid.Term.typ in
    (cidTerm, Convert.typToClause tM)

  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.name

  let storeType cId =
    let typEntry = Cid.Typ.get cId in
    let typConstr = typEntry.Cid.Typ.constructors in
    let entType = addType cId in
    let storeTmCl cidTerm =
      addClause entType (clausifyTerm cidTerm) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in revIter storeTmCl typConstr

  let storeQueryTyp (tM, i) =
    addQuery (Convert.typToQuery (tM, i))

  let robStore () =
    List.iter storeType !Cid.Typ.entry_list

end


module Printer = struct

  module P = Pretty.Int.DefaultPrinter

  open Printf

  let nameToString x = x.Id.string_of_name

  let dctxToString cPsi = 
    P.dctxToString LF.Empty LF.Empty cPsi

  let typToString cPsi sM =
    P.typToString LF.Empty LF.Empty cPsi sM

  let declToString cPsi (typDecl, s) = match typDecl with
    | LF.TypDecl (x, tM) -> nameToString x ^ ":" ^ typToString cPsi (tM, s)
    | _ -> invalid_arg
      "Logic.Printer.declToString: Match failure against LF.TypDecl (_,_)."

  let rec goalToString cPsi (g, s) = match g with
    | Atom (tA) ->
      typToString cPsi (tA, s)
    | Impl ((r, typDecl), g') ->
      resToString cPsi (r, s) ^ " -> " ^ goalToString 
        (LF.DDec (cPsi, S.LF.decSub typDecl s)) (g', S.LF.dot1 s)
    | All (typDecl, g') ->
      "[∀" ^ declToString cPsi (typDecl, s) ^ ". " ^ goalToString 
        (LF.DDec (cPsi, S.LF.decSub typDecl s)) (g', S.LF.dot1 s) ^ "]"

  and resToString cPsi (r, s) = match r with
    | Head (tH) ->
      typToString cPsi (tH, s)
    | And (g, r') ->
      goalToString cPsi (g, s) ^ " -> " ^ resToString cPsi (r', s)
    | Exists (LF.TypDecl (_, tM) as typDecl, r') ->
      let tM' = Convert.etaExpand cPsi (tM, s) in
      "[∃" ^ declToString cPsi (typDecl, s) ^ ". " ^ resToString
        cPsi (r', LF.Dot (LF.Obj tM', s)) ^ "]"

  let printClause cPsi (cl, s) =
    let rec printGoals gC = match gC with
      | LF.Empty -> ()
      | LF.Dec (gC', g) ->
        printf "  <- %s\n" (goalToString cl.cVars (g, s)) ;
        printGoals gC' in
    begin
      printf "%s\n" (typToString cl.cVars (cl.tHead, s)) ;
      printGoals cl.gCtx
    end

  let printDynCl cPsi (cl, s) =
    let rec printGoals gC = match gC with
      | LF.Empty -> ()
      | LF.Dec (gC', g) ->
        printf "  <- %s\n" (goalToString cPsi (g, s)) ;
        printGoals gC' in
    begin
      printf "%s\n" (typToString cPsi (cl.tHead, s)) ;
      printGoals cl.gCtx
    end

  let printEntClause (cidTerm, cl) =
    printf "%s: " (nameToString (Persist.termName cidTerm)) ; 
    printClause LF.Null (cl, S.LF.id) ; print_newline ()

  let printQuery (g, s) =
    printf "%%query %s\n" (goalToString LF.Null (g, s))

end


module Solver = struct

  module U = Unify.StdTrail

  type dpool = 
    | Empty
    | DynCl of dpool * (clause * int)

  let unifyTyp cPsi sA sB sc =
    try U.unifyTyp LF.Empty cPsi sA sB ;
        sc ()
    with U.Unify (message) -> ()

  let idEqual tM dCl = match (tM, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) ->
      i = j
    | _ -> invalid_arg
      "Logic.Solver.idEqual: Match failure against LF.Atom (_,_,_)."

  let atomIdTyp tM = match tM with
    | LF.Atom (_, i, _) -> i
    | _ -> invalid_arg
      "Logic.Solver.atomIdTyp: Match failure against LF.Atom (_,_,_)."

  let rec gSolve dPool (cPsi, k) (g, s) sc = match g with
    | Atom (tA) ->
      matchAtom dPool (cPsi, k) (tA, s) sc
    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
      let dPool' = DynCl (dPool, (Convert.resToClause (r, s), k)) in
      gSolve dPool' (LF.DDec (cPsi, S.LF.decSub tD s), k + 1)
        (g', S.LF.dot1 s) (* sc  *)
        (function tM -> sc (LF.Lam (None, x, tM)))
    | All (LF.TypDecl (x, _) as tD, g') ->
      gSolve dPool (LF.DDec (cPsi, S.LF.decSub tD s), k + 1) (g', S.LF.dot1 s)
        (* sc *) (function tM -> sc (LF.Lam (None, x, tM)))

  and matchAtom dPool (cPsi, k) (tA, s) sc =
    let matchEntCl (cidTerm, cl) =
      let (s', sFn) = Convert.dctxToSubPT cPsi cl.cVars 
        (LF.Shift (LF.NoCtxShift, Context.dctxLength cPsi)) 
        (function tS -> tS) in
      unifyTyp cPsi (tA, s) (cl.tHead, s')
        (function () -> ctxSolve dPool (cPsi, k) (cl.gCtx, s') (* sc *)
          (function tS -> 
            sc (LF.Root (None, LF.Const(cidTerm), sFn tS)))) in

    let rec matchClause dPool = match dPool with
      | Empty ->
        DynArray.iter matchEntCl
          (Persist.lookupType (atomIdTyp tA))
      | DynCl (dPool', (dCl, k')) ->
        if (idEqual tA dCl) then
          let (s', sFn) = Convert.dctxToSubPT cPsi dCl.cVars 
            (LF.Shift (LF.NoCtxShift, k - k')) (function tS -> tS) in
          dmesg ("cPsi: " ^ Printer.dctxToString cPsi) ;
          dmesg ("cVars: " ^ Printer.dctxToString dCl.cVars) ;
          unifyTyp cPsi (tA, s) (dCl.tHead, s')
            (function () -> ctxSolve dPool (cPsi, k) (dCl.gCtx, s') (* sc *)
              (function tS -> sc (LF.Root (None, LF.BVar(k - k'), sFn tS)))) ;
          matchClause dPool'
        else matchClause dPool' in
    matchClause dPool

  and ctxSolve dCls (cPsi, k) (gCtx, s) sc = match gCtx with
    | LF.Empty -> sc (* () *) LF.Nil
    | LF.Dec (gCtx', g) ->
      gSolve dCls (cPsi, k) (g, s)
        (* (function () -> ctxSolve dCls (cPsi, k) (gCtx', s) (\* sc *\)) *)
          (function tM -> ctxSolve dCls (cPsi, k) (gCtx', s) 
            (function tS -> sc (LF.App (tM, tS))))
          
  let qSolve (g, s) sc =
    gSolve Empty (LF.Null, 0) (g, s) sc

end

let logicEnabled = ref false

let storeQueryTyp (tM, i) = 
  Persist.storeQueryTyp (tM, i)

let buildPersist () =
  if !logicEnabled then
    begin
      Persist.robStore () ;
      Hashtbl.iter (function _ -> function dynArr ->
        DynArray.iter Printer.printEntClause dynArr) Persist.tblTypes ;
      DynArray.iter (function (g, s) -> 
        Printer.printQuery (g, s) ;
        Solver.qSolve (g, s) (function tM -> 
          print_endline (Pretty.Int.DefaultPrinter.normalToString LF.Empty LF.Empty LF.Null (tM, S.LF.id))))
        Persist.arrQueries
    end
  else ()
