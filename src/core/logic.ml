(* module Logic *)
(* author:
   Costin Badescu
   Jacob Thomas Errington
 *)

module S = Substitution.LF
open Printf
open Syntax.Int


module Options = struct

  (* Enable the logic programming engine (disabled by default). *)
  let enableLogic = ref true

  (* Control verbosity level:
       0 => No output.
       1 => Query and success notification.
       2 => + Error messages.
       3 => + Solutions and proof terms.
       4 => + LF signature.
  *)
  let chatter = ref 3

  (* Ask before giving more solutions (à la Prolog). *)
  let askSolution = ref false

  (* Type check the proof terms. *)
  let checkProofs = ref false

end


(* Naming conventions:
     g : goal
   Goal.
     r : res
   Residual goal.
     cPsi : LF.dctx
   Universal typing context.
     tD : typ_decl
   LF type declaration.
     dPool : dPool
   Pool of dynamic assumptions.
     cG : conjunction
   Conjunction of goals.
     eV : LF.dctx
   Context with TypDecl's of existential variables belonging to a clause.
     dCl : clause
   Dynamic clause.
     sCl : clause
   Clause from LF signature.
     cS : int
   Constant shift for BVar indices bound to existential variables.
     dS : int
   Dynamic shift for indices of variables in dynamic clauses.
     dR : int
   Range of de Bruijn indices in the dynamic scope.
*)


type goal =                             (* Goals            *)
  | Atom of LF.typ                      (* g ::= A          *)
  | Impl of (res * LF.typ_decl) * goal  (*     | r => g'    *)
  | All of LF.typ_decl * goal           (*     | ∀x:A. g'   *)

and res =                               (* Residual Goals   *)
  | Head of LF.typ                      (* r ::= A          *)
  | And of goal * res                   (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:T. r'   *)

type conjunction =                      (* Subgoals         *)
  | True                                (* cG ::= True      *)
  | Conjunct of conjunction * goal      (*      | cG' ∧ g   *)

type bound = int option                 (* b ::= '*' | nat  *)

and query = (goal * LF.sub)             (* q ::= (g, s)     *)

type clause =                    (* Horn Clause ::= eV |- A :- cG   *)
    { tHead : LF.typ             (* Head A : LF.Atom                *)
    ; eVars : LF.dctx            (* Context eV : EV's bound in A/cG *)
    ; subGoals : conjunction }   (* Subgoals cG : solv. cG => A     *)


module Shift : sig

  val shiftAtom : LF.typ -> (int * int * int) -> LF.typ

end = struct

  (* NB.

     Only BVar's in LF.Atom's are affected.
     Enclosed substitutions are not shifted.

     i: De Bruijn index.
     k: Shifting measure.

     Algorithm:

     BV bound by λ remain invariant.
      - i < lR |- BV(i) -> BV(i)

     BV bound by a dynamic scope are shifted by dS.
      - lR < i <= dR |- BV(i) -> BV(i + dS)

     BV bound to EV are shifted by k.
      - i > lR && i > dR |- BV(i) -> BV(i + k)
  *)

  let lR = ref 0               (* Range of Lambda Scope *)
  let dR = ref 0               (* Range of Dynamic Scope *)
  let dS = ref 0               (* Dynamic Shift *)

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

  (* typToClause' eV cG M (cS, dS, dR) = clause
     Invariants:
       If BV(i) is free in M, then BV(i) is bound in (eV |- M).
       If M = PiTyp (x:A, No), then M ~ g.
  *)
  let rec typToClause' eV cG tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      typToClause' (LF.DDec (eV, tD)) cG tM' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl(_, tA), LF.No), tB) ->
      typToClause' eV (Conjunct (cG, typToGoal tA (cS, dS, dR)))
        tB (cS + 1, dS, dR)
    | LF.Atom (_) as tA ->
      { tHead = (Shift.shiftAtom tA (-cS, -dS, dR))
      ; eVars = eV
      ; subGoals = cG }

  and typToGoal tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      All (tD, typToGoal tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tD, LF.No), tB) ->
      Impl ((typToRes tA (cS, dS, dR), tD), typToGoal tB
        (cS, dS, dR + 1))
    | LF.Atom (_) as tA ->
      Atom (Shift.shiftAtom tA (-cS, -dS, dR))

  and typToRes tM (cS, dS, dR) = match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
      Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
      And (typToGoal tA (cS, dS, dR), typToRes tB
        (cS + 1, dS + 1, dR + 1))
    | LF.Atom (_) as tA ->
      Head (Shift.shiftAtom tA (-cS, -dS, dR))

  let rec resToClause' eV cG (r, s) = match r with
    | Exists (tD, r') ->
      resToClause' (LF.DDec (eV, tD)) cG (r', S.dot1 s)
    | And (g, r') ->
      resToClause' eV (Conjunct (cG, g)) (r', s)
    | Head (tA) ->
      let (tA', _) = Whnf.whnfTyp (tA, s) in
      { tHead = tA' ; eVars = eV ; subGoals = cG }

  let resToClause (r, s) =
    resToClause' LF.Null True (r, s)

  let typToClause tM =
    typToClause' LF.Null True tM (0, 0, 0)

  (* etaExpand Psi (A, s) = normal
     Invariants:
       Psi |- s : Phi
       Phi |- A : LF.typ

     Effects:
       None.
  *)
  let rec etaExpand cD cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA
    in match tA with
      | LF.Atom (_) as tA ->
        let u = LF.Inst (Whnf.newMMVar None (cD, cPsi, LF.TClo (tA, s)) LF.Maybe) in
        LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil)
      | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
         LF.Lam (
             Syntax.Loc.ghost, x,
             etaExpand cD (LF.DDec (cPsi, S.decSub tD s)) (tB, S.dot1 s))

  (* dctxToSub Delta Psi (eV, s) fS = sub * (spine -> spine)
     Invariants:
       eV = Null | ((Null, Dec (x, M)), ...)
       Psi |- s : Phi
       Phi |- M
       fS : spine -> spine

     Effects:
       None.

     Create MVars for all the TypDecl's in eV. Accumulate them
     in a substitution, performing eta-expansion if necessary,
     and add them to the spine of a proof-term through fS.
  *)
  let rec dctxToSub cD cPsi (eV, s) fS = match eV with
    | LF.DDec (eV', LF.TypDecl (_, tM)) ->
      let (s', fS') = dctxToSub cD cPsi (eV', s) fS in
      let tM' = etaExpand cD cPsi (tM, s') in
      (LF.Dot (LF.Obj tM', s'), (fun tS -> fS' (LF.App (tM', tS))))
    | LF.Null -> (s, fS)
    | LF.CtxVar (_) -> invalid_arg
        "Logic.Convert.dctxToSub: Match conflict with LF.CtxVar (_)."

  (* typToQuery (M, i)  = ((g, s), xs)
     Transform a reconstructed LF.typ into a query, accumulating all
     the abstracted existential variables into a substitution while
     storing the MVars into a list `xs' for immediate access.
  *)
  let typToQuery cPsi cD (tA, i) =
    let rec typToQuery' (tA, i) s xs = match tA with
      | LF.PiTyp ((LF.TypDecl (x, tA), LF.Maybe), tB) when i > 0 ->
        let tN' = etaExpand cD cPsi (tA, s) in
        typToQuery' (tB, i - 1) (LF.Dot (LF.Obj tN', s))
          ((x, tN') :: xs)
      | _ -> ((typToGoal tA (0, 0, 0), s), tA, s, xs)
    in typToQuery' (tA, i) S.id []

  let rec solToSub xs = match xs with
    | [] -> S.id
    | (x, tN) :: xs -> LF.Dot (LF.Obj tN, solToSub xs)

end


module Index = struct

  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  type inst = (Id.name * LF.normal)     (* I ::= (x, MVar)             *)

  and sgnQuery =
      { query : query                   (* Query ::= (g, s)            *)
      ; typ : LF.typ                    (* Query as LF.typ.            *)
      ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
      ; optName : Id.name option        (* Opt. name of proof term.    *)
      ; expected : bound                (* Expected no. of solutions.  *)
      ; tries : bound                   (* No. of tries to find soln.  *)
      ; instMVars : inst list }         (* MVar instantiations.        *)

  let queries = DynArray.create ()      (* sgnQuery DynArray.t         *)

  let querySub = ref S.id

  (* addTyp c = sgnClause DynArray.t
     Create a new entry for a type constant, c, in the `types' table and
     return it's mapping, i.e. an empty DynArray.
  *)
  let addTyp cidTyp =
    Hashtbl.add types cidTyp (DynArray.create ()) ;
    Hashtbl.find types cidTyp

  (* addSgnClause tC, sCl = ()
     Add a new sgnClause, sCl, to the DynArray tC.
  *)
  let addSgnClause typConst sgnClause =
    DynArray.add typConst sgnClause

  (* addSgnQuery (p, (g, s), xs, e, t)  = ()
     Add a new sgnQuery to the `queries' DynArray.
  *)
  let addSgnQuery (p, a, a', q, xs, e, t) =
    DynArray.add queries
      { query = q ;
        typ = a ;
        skinnyTyp = a' ;
        optName = p ;
        expected = e ;
        tries = t ;
        instMVars = xs }

  (* compileSgnClause c = (c, sCl)
     Retrieve LF.typ for term constant c, clausify it into sCl and
     return an sgnClause (c, sCl).
  *)
  let compileSgnClause cidTerm =
    let termEntry = Cid.Term.get cidTerm in
    let tM = termEntry.Cid.Term.typ in
    (cidTerm, Convert.typToClause tM)

  (* termName c = Id.name
     Get the string representation of term constant c.
  *)
  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.name

  (* storeTypConst c = ()
     Add a new entry in `types' for type constant c and fill the DynArray
     with the clauses corresponding to the term constants associated with c.
     The revIter function serves to preserve the order of term constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeTypConst cidTyp =
    let typEntry = Cid.Typ.get cidTyp in
    let typConstr = !(typEntry.Cid.Typ.constructors) in
    let typConst = addTyp cidTyp in
    let regSgnClause cidTerm =
      addSgnClause typConst (compileSgnClause cidTerm) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in revIter regSgnClause typConstr

  (* storeQuery (p, (M, i), e, t) = ()
     Invariants:
       i = count of abstracted EVars in M
  *)
  let storeQuery (p, (tM, i), e, t) =
    let (q, tM', s, xs) = (Convert.typToQuery LF.Null LF.Empty (tM, i)) in
    ignore (querySub := s) ; addSgnQuery (p, tM, tM', q, xs, e, t)

  (* robStore () = ()
     Store all type constants in the `types' table.
  *)
  let robStore () =
    try
      List.iter storeTypConst !(DynArray.get Cid.Typ.entry_list !(Modules.current))
    with _ -> ()

  (* iterSClauses f c = ()
     Iterate over all signature clauses associated with c.
  *)
  let iterSClauses f cidTyp =
    DynArray.iter f (Hashtbl.find types cidTyp)

  let iterAllSClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) types

  let iterQueries f =
    DynArray.iter (fun q -> f q) queries

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = DynArray.clear queries ; Hashtbl.clear types


  let singleQuery (p, (tM, i), e, t) f =
    let (q, tM', s, xs) = (Convert.typToQuery LF.Null LF.Empty (tM, i)) in
    ignore (querySub := s) ;
    robStore();
    let bchatter = !Options.chatter in
    Options.chatter := 0;
    let sgnQ = { query = q ;
        typ = tM ;
        skinnyTyp = tM' ;
        optName = p ;
        expected = e ;
        tries = t ;
        instMVars = xs } in
    f sgnQ;
    Options.chatter := bchatter;
   Hashtbl.clear types


end


module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  let dctxToString cPsi =
    P.dctxToString LF.Empty cPsi

  let typToString cD cPsi sM =
    P.typToString cD cPsi sM

  let normalToString cPsi sM =
    P.normalToString LF.Empty cPsi sM

  let declToString cD cPsi (tD, s) = match tD with
    | LF.TypDeclOpt x ->
      Id.string_of_name x ^ ":_"
    | LF.TypDecl (x, tM) ->
      Id.string_of_name x ^ ":" ^ typToString cD cPsi (tM, s)

  (* goalToString Psi (g, s) = string
     Invariants:
       Psi |- s : Phi
       Phi |- g : goal
       Psi |- g[s] : goal

     Effects:
       None.
  *)
  let rec goalToString cD cPsi (g, s) = match g with
    | Atom (tA) ->
       typToString cD cPsi (tA, s)
    | Impl ((r, tD), g') ->
       sprintf "%s -> %s"
         (resToString cD cPsi (r, s))
         (goalToString cD (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s))
    | All (tD, g') ->
       sprintf "[∀%s. %s]"
         (declToString cD cPsi (tD, s))
         (goalToString cD (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s))

  (* resToString cPsi (r, s) = string
     Invariants:
       Psi |- s: Phi
       Phi |- r : res
       Psi |- r[s] : res

     Effects:
       None.
  *)
  and resToString cD cPsi (r, s) = match r with
    | Head (tH) ->
      typToString cD cPsi (tH, s)
    | And (g, r') ->
       sprintf "%s -> %s"
         (goalToString cD cPsi (g, s))
         (resToString cD cPsi (r', s))
    | Exists (LF.TypDecl (_, tM) as tD, r') ->
       let tM' = Convert.etaExpand cD cPsi (tM, s) in
       sprintf "[∃%s. %s]"
         (declToString cD cPsi (tD, s))
         (resToString cD cPsi (r', LF.Dot (LF.Obj tM', s)))

  let rec subGoalsToString cD cPsi (cG, s) = match cG with
    | True -> ""
    | Conjunct (cG', g) ->
       sprintf "  <- %s\n%s"
         (goalToString cD cPsi (g, s))
         (subGoalsToString cD cPsi (cG', s))

  (* sgnClauseToString (c, sCl) = string
     String representation of signature clause.
  *)
  and sgnClauseToString (cidTerm, sCl) =
    sprintf "%s: %s\n%s"
      (Id.string_of_name (termName cidTerm))
      (typToString LF.Empty sCl.eVars (sCl.tHead, S.id))
      (subGoalsToString LF.Empty sCl.eVars (sCl.subGoals, S.id))

  let boundToString b = match b with
    | Some i -> string_of_int i
    | None -> "*"

  let sgnQueryToString q =
    sprintf "--query %s %s\n\n%s"
      (boundToString q.expected)
      (boundToString q.tries)
      (typToString LF.Empty LF.Null (q.typ, S.id))

  (* instToString xs = string
     Return string representation of existential variable
     instantiations in the query.
  *)
  let rec instToString xs = match xs with
    | ((x, tM) :: []) -> sprintf "%s = %s."
      (Id.string_of_name x)
      (normalToString LF.Null (tM, S.id))
    | ((x, tM) :: ys) -> sprintf "%s = %s;\n%s"
      (Id.string_of_name x)
      (normalToString LF.Null (tM, S.id))
      (instToString ys)
    | [] -> "Empty substitution."

  let printQuery q =
    printf "%s.\n\n" (sgnQueryToString q)

  let printSignature () =
    iterAllSClauses (fun w -> printf "%s\n" (sgnClauseToString w))

end


module Solver = struct

  module U = Unify.StdTrail
  module C = Convert
  module I = Index

  (* Dynamic Assumptions *)
  type dPool =                           (* dP ::=                  *)
    | Empty                              (*      | Empty            *)
    | DynCl of (dPool * (clause * int))  (*      | (dP', (dCl, k))  *)

  (* unify Psi (A, s) (B, s') sc = ()
     Invariants:
       sc : unit -> unit

     Effects:
       Instatiation of MVars in s and s'.
       Any effect of (sc ()).
  *)
  let unify cD cPsi sA sB sc =
    U.unifyTyp cD cPsi sA sB ; sc ()

  (* trail f = ()
     Trail a function. If an exception is raised, unwind the trail and
     propagate the exception.
  *)
  let trail f =
    let () = U.mark () in
    try f () ; U.unwind () with e -> (U.unwind (); raise e)

  (* eqHead A dCl = bool
     Compare the cid_typ's of A and the head of dCl.
  *)
  let eqHead tM dCl = match (tM, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) ->
      i = j
    | _ -> false

  (* cidFromAtom A = cid_typ *)
  let cidFromAtom tM = match tM with
    | LF.Atom (_, i, _) -> i
    | _ -> invalid_arg
      "Logic.Solver.cidFromAtom: Match failure against LF.Atom (_,_,_)."

  (* shiftSub k = ^k
     Invariants:
       Psi, x1:_, x2:_, ... xk:_ |- ^k : Psi
  *)
  let shiftSub k = LF.Shift k

  (* gSolve dPool (Psi, k) (g, s) sc = ()
     Invariants:
       dPool ~ Psi
       k = |Psi|
       Psi |- s : Phi
       Phi |- g : Goal
       sc : proof -> unit
       If G |- M : g[s], then (sc M) is evaluated.

     Effects:
       Instantiation of MVars in s and dPool.
       Any effect (sc M) might have.

     Comments:
       In the arguments to 'sc', 'u' refers to the universal
       context and 't' refers to a proof term.
  *)
  let rec gSolve dPool cD (cPsi, k) (g, s) sc = match g with
    | Atom (tA) ->
      matchAtom dPool cD (cPsi, k) (tA, s) sc
    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
      let dPool' = DynCl (dPool, (C.resToClause (r, s), k)) in
      gSolve dPool' cD (LF.DDec (cPsi, S.decSub tD s), k + 1)
        (g', S.dot1 s) (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))
    | All (LF.TypDecl (x, _) as tD, g') ->
      gSolve dPool cD (LF.DDec (cPsi, S.decSub tD s), k + 1)
        (g', S.dot1 s) (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

  (* matchAtom dPool (Psi, k) (A, s) sc = ()
     Invariants:
       dPool ~ Psi, k = |Psi|
       Psi |- s : Phi
       Phi |- A : Atom
       sc : proof -> unit
       If Psi |- M : A[s], then (sc M) is evaluated.

     Effects:
       Instatiation of MVars in s and dPool.
       Any effect (sc M) might have.
  *)
  and matchAtom dPool cD (cPsi, k) (tA, s) sc =
    (* some shorthands for creating syntax *)
    let root x = LF.Root (Syntax.Loc.ghost, x, LF.Nil) in
    let pvar k = LF.PVar (k, LF.Shift 0) in
    let mvar k = LF.MVar (LF.Offset k, LF.Shift 0) in
    let proj x k = LF.Proj (x, k) in

    (* matchDProg dPool = ()
       Try all the dynamic clauses in dPool starting with the most
       recent one. If dPool is empty, try the signature.
    *)
    let rec matchDProg dPool = match dPool with
      | DynCl (dPool', (dCl, k')) ->
        if (eqHead tA dCl) then
          let (s', fS) =
            C.dctxToSub cD cPsi (dCl.eVars, shiftSub (k - k'))
              (fun tS -> tS) in
          (* Trail to undo MVar instantiations. *)
          (try trail (fun () -> unify cD cPsi (tA, s) (dCl.tHead, s')
            (fun () -> solveSubGoals dPool cD (cPsi, k) (dCl.subGoals, s')
              (fun (u, tS) ->
                sc (u, LF.Root (Syntax.Loc.ghost, LF.BVar (k - k'), fS (spineFromRevList tS))))))
           with U.Failure _ -> ()) ; matchDProg dPool'
        else matchDProg dPool'
      | Empty ->
        matchSig (cidFromAtom tA)

    (* Decides whether the given Sigma type can solve the
     * goal type by trying all the projections.
     * Calls the success continuation with the found index.
     *
     * pv: the pattern variable whose sigma type we are analyzing
     * cD, psi: the contexts in which pv makes sense
     * typs: the sigma type of pv that we are analyzing
     * ts: the substitution we build up for past projections.
     * Since typs is a dependent pair, later projections can depend on
     * earlier projections. Hence, when we try to unify a later
     * projection with the goal type, we need to eliminate its bound
     * variables by substituting in the appropriate earlier projections.
     *)
    and matchSigma (pv : LF.head) (cD : LF.mctx) (psi : LF.dctx) ((typs, ts) : LF.typ_rec * LF.sub) (k : int) sc : unit =
      let check typ =
        try
          trail (fun () ->
              (*
              Format.printf "[matchSigma] %s ~=~ %s ?\n"
                (Printer.P.typToString cD psi (typ, ts))
                (Printer.P.typToString cD psi (tA, s));
               *)
              (* We added k-1 entries to psi at this point, so we need
                 to weaken the goal type by k-1 before trying to
                 unify. *)
              U.unifyTyp cD psi (typ, ts) (tA, s);
              sc k)
        with
        | U.Failure s -> ()
      in
      match typs with
      | LF.SigmaLast (name, typ) ->
         check typ
      | LF.SigmaElem (name, typ, typs) ->
         check typ;
         (* extend the substitution to use on subsequent entries of the sigma.
          *)
         matchSigma
           pv
           cD
           psi
           (typs, LF.Dot (LF.Head (proj pv k), ts))
           (k + 1)
           sc

    (* Try to find a solution in the meta-context.
     * The index `k` is the position we're looking at currently,
       and is used to appropriately weaken the meta-context type
       so that it is in the same context as the goal.
     * The initial value for `k` is 1.
     * If the context entry fails to unify with the target type,
       then this function will check whether the context entry is
       a Sigma type, meaning that it is a pattern or bound
       variable.
     * In that case, it will call matchSigma to figure out the
       appropriate projection to use on the variable, if any.
     *)
    and matchDelta (cD' : LF.mctx) (k : int) =
      match cD' with
      | LF.Empty -> matchDProg dPool
      | LF.Dec (cD', LF.Decl (_, LF.ClTyp (cltyp, psi), _)) ->
         begin
           let psi' = Whnf.cnormDCtx (psi, LF.MShift k) in
           let cltyp' = Whnf.cnormClTyp (cltyp, LF.MShift k) in
           try
             trail
               begin fun () ->
               U.unifyDCtx cD psi' cPsi;
               (* We look to see whether we're dealing with a sigma type.
                  In this case, we must consider the projections of the sigma.
                  If it isn't a sigma then we can just try to unify the types.
                *)
               match cltyp' with
               | LF.PTyp (LF.Sigma typs) ->
                  matchSigma (pvar k) cD psi' (typs, LF.Shift 0) 1
                    (fun k' ->
                      (* recall: k is the index of the variable in the _context_ *)
                      (* k' is the index of the projection into the _sigma_ *)
                      sc (psi', root (proj (pvar k) k'))
                    )

               | LF.PTyp typ' ->
                  (* I don't think this case ever happens; I'm pretty
                   * sure that whenever we have a PTyp, its type is a
                   * Sigma, so we can probably remove this case or assert
                   * that it's impossible.
                   * -jake
                   *)

                  U.unifyTyp cD psi' (typ', LF.Shift 0) (tA, s);

                  (* We need to create the syntax to refer to this _pattern_ variable *)
                  sc (psi', root (pvar k))

               | LF.MTyp typ' ->
                  U.unifyTyp cD psi' (typ', LF.Shift 0) (tA, s);

                  (* We need to create the syntax to refer to this _meta_ variable *)
                  sc (psi', root (mvar k))
               end
           with
           | U.Failure s -> ()
         end;
         matchDelta cD' (k + 1)

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
    *)
    and matchSig cidTyp =
      I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the head of sCl with A[s]. If unification succeeds,
       attempt to solve the subgoals of sCl.
    *)
    and matchSgnClause (cidTerm, sCl) sc =
      let (s', fS) =
        C.dctxToSub cD cPsi (sCl.eVars, shiftSub (Context.dctxLength cPsi))
          (fun tS -> tS) in
      (* Trail to undo MVar instantiations. *)
      try
        trail
          ( fun () ->
            U.unifyTyp cD cPsi (tA, s) (sCl.tHead, s');
            solveSubGoals dPool cD (cPsi, k) (sCl.subGoals, s')
              ( fun (u, tS) ->
                sc
                  ( u
                  , LF.Root
                      ( Syntax.Loc.ghost
                      , LF.Const (cidTerm)
                      , fS (spineFromRevList tS)))))
      with U.Failure _ -> ()
    in
    (* ^ end of the gigantic let of all the helpers for matchAtom;
     * Now here's the actual body of matchAtom: *)
    matchDelta cD 1

(* spineFromRevList : LF.normal list -> LF.spine
  build an LF.spine out of a list of LF.normal, reversing the order of the elements*)
  and spineFromRevList lS =
      List.fold_left (fun tSc tMc -> LF.App(tMc, tSc)) LF.Nil lS

  (* solveSubGoals dPool (Psi, k) (G, s) sc = ()
     Invariants:
       dPool ~ Psi
       G = (G', g) | T
       Psi |- s : Phi
       Phi |- g : goal
       sc : (dctx * spine) -> unit
       If Psi |- M : g[s], then (sc App (M, S)) is evaluated.
       If Psi |- G = T, then (sc Nil) is evaluated, ending the
       spine of proof-terms for the goals in G.

     Effects:
       Instatiation of MVars in dPool and g[s].
       Any effect of (sc S).
  *)
  and solveSubGoals dPool cD (cPsi, k) (cG, s) sc = match cG with
    | True -> sc (cPsi, [])
    | Conjunct (cG', g) ->
      gSolve dPool cD (cPsi, k) (g, s)
        (fun (u, tM) -> solveSubGoals dPool cD (cPsi, k) (cG', s)
          (fun (v, tS) -> sc (v, tM::tS)))

  (* solve (g, s) sc = ()
     Invariants:
       Empty |- g[s] : goal
       sc : dctx * normal -> unit

     Effects:
       Same as gSolve.
  *)
  let solve cD cPsi (g, s) sc =
    gSolve Empty cD (cPsi, Context.dctxLength cPsi) (g, s) sc
end

module Frontend = struct

  module P = Printer
  open Index

  exception Done                        (* Solved query successfully. *)
  exception AbortQuery of string        (* Abort solving the query.   *)

  (* exceeds B1 B2 = b
     True if B1 = * or B1 >= B2.
  *)
  let exceeds x y = match (x, y) with
    | (Some i, Some j) -> i >= j
    | (Some i, None) -> false
    | (None, _) -> true

  (* boundEq B1 B2 = b
     Equality function for bounds.
  *)
  let boundEq x y = match (x, y) with
    | (Some i, Some j) -> i = j
    | (None, None) -> true
    | (_, _) -> false

  (* lowerBound B1 B2 = min (B1, B2) *)
  let lowerBound x y = match (x, y) with
    | (Some i, Some j) -> Some (min i j)
    | (x, None) -> x
    | (None, y) -> y

  (* Abort query. *)
  let abort s = raise (AbortQuery s)

  (* checkSolutions e t s = () *)
  let checkSolutions e t s = match (e, t) with
    | (None, None) -> ()
    | _ ->
      if not (boundEq (lowerBound e t) (Some s)) then
        abort ("Query error: Wrong number of solutions -- "
               ^ "expected " ^ (P.boundToString e) ^ " in "
               ^ (P.boundToString t) ^ " tries, but found "
               ^ (string_of_int s))
      else ()

  (* moreSolutions () = () *)
  let moreSolutions () =
    printf "More? " ; match (read_line ()) with
      | "y" | "Y" | ";" -> true
      | "q" | "Q" -> abort "Query error -- explicit quit."
      | _ -> false

  (* solve q = () *)
  let solve sgnQuery =

    (* Keep track of no. of solutions found. *)
    let solutions = ref 0 in

    (* Type checking function. *)
    let check cPsi tM s = Check.LF.check LF.Empty
      cPsi (tM, S.id) (sgnQuery.skinnyTyp, s) in


    (* Initial success continuation. *)
    let scInit (cPsi, tM) =
      ignore (incr solutions) ;

      (* Rebuild the substitution and type check the proof term. *)
      if !Options.checkProofs then
        check cPsi tM (Convert.solToSub sgnQuery.instMVars) (* !querySub *)
      else () ;

      (* Print MVar instantiations. *)
      if !Options.chatter >= 3 then
        begin
          printf "---------- Solution %d ----------\n[%s]\n%s\n"
            !solutions (P.dctxToString cPsi)
            (P.instToString sgnQuery.instMVars) ;
          (* Print proof term. *)
          (match sgnQuery.optName with
            | Some n ->
              printf "%s\n" (P.instToString [(n, tM)])
            | None -> ()) ;
          printf "\n"
        end
      else () ;
      (* Interactive. *)
      if !Options.askSolution then
        if moreSolutions () then () else raise Done
      else () ;
      (* Stop when no. of solutions exceeds tries. *)
      if exceeds (Some !solutions) sgnQuery.tries then
        raise Done
      else ()
    in

    if not (boundEq sgnQuery.tries (Some 0)) then
      begin
        if !Options.chatter >= 1 then
          P.printQuery sgnQuery
        else () ;
        try

          Solver.solve LF.Empty LF.Null sgnQuery.query scInit ;
          (* Check solution bounds. *)
          checkSolutions sgnQuery.expected sgnQuery.tries !solutions
        with
          | Done -> printf "Done.\n"
          | AbortQuery (s) -> printf "%s\n" s
          | _ -> ()
      end

    else if !Options.chatter >= 2 then
      printf "Skipping query -- bound for tries = 0.\n"

    else ()

end


(* Interface *)

let storeQuery p (tM, i) e t =
  Index.storeQuery (p, (tM, i), e, t)

(* runLogic () = ()
   If !enabledLogic, run the logic programming engine. Otherwise
   do nothing, i.e. return unit.
*)
let runLogic () =
  if !Options.enableLogic then
    begin
      (* Transform LF signature into clauses. *)
      Index.robStore () ;
      (* Optional: Print signature clauses. *)
      if !Options.chatter >= 4 then
        Printer.printSignature ()
      else () ;
      (* Solve! *)
      Index.iterQueries Frontend.solve ;
      (* Clear the local storage.  *)
      Index.clearIndex ()
    end
  else () (* NOP *)


let runLogicOn n (tA,i) e t  =
  Index.singleQuery (n,(tA,i),e,t) Frontend.solve

let prepare () =
  Index.clearIndex () ;
  Index.robStore ()

(* 


let runLogicOn n (cD, cPsi, tA, i) e t  =
  Index.singleQuery (n,(tA,i),e,t) Frontend.solve
 *)
