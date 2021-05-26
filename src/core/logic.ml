open Support.Equality
(* module Logic *)
(* author:
   Costin Badescu
   Jacob Thomas Errington
 *)

open Support
module S = Substitution.LF
open Format
open Syntax.Int

let (dprintf, _, _) = Debug.makeFunctions' (Debug.toFlags [11])
open Debug.Fmt

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
  let chatter = ref 4

  (* Ask before giving more solutions (à la Prolog). *)
  let askSolution = ref false

  (* Type check the proof terms. *)
  let checkProofs = ref false
end


exception NotImplementedYet 

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
     sCCl : clause 
   Clause from Signature of computation type. 
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
  | Comp of Comp.typ                    (*     | [ g' ]     *)

and res =                               (* Residual Goals   *)
  | Head of LF.typ                      (* r ::= A          *)
  | And of goal * res                   (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:T. r'   *)

type conjunction =                       (* Subgoals         *)
  | True                                 (* cG ::= True      *)
  | Conjunct of conjunction * goal       (*      | cG' ∧ g   *) 

let rec list_of_conjunction : conjunction -> goal list =
  function
  | True -> []
  | Conjunct (c, x) -> x :: list_of_conjunction c

type bound = int option                 (* b ::= '*' | nat  *)

type query = goal * LF.sub              (* q ::= (g, s)     *)

type clause =                    (* Horn Clause ::= eV |- A :- cG   *)
  { tHead : LF.typ               (* Head A : LF.Atom                *)
  ; eVars : LF.dctx              (* Context eV : EV's bound in A/cG *)
  ; subGoals : conjunction       (* Subgoals cG : solv. cG => A     *)
  }

(* Naming conventions:

  cg : comp_goal (computation-level goal)
  mq : mquery    (a query for a cg) 

 *)

type comp_goal =
  | Box of  LF.dctx  * goal
  | Implies of comp_goal * comp_goal  
  | Forall of  LF.ctyp_decl * comp_goal         

type mquery = comp_goal * LF.msub       (* mq := (cg, ms)  *)

type cclause =                       (* Horn Clause ::= cD [eV |- A :- cG]  *)
  { ctHead : LF.typ                  (* Head A : LF.typ                     *)
  ; cEVars : LF.dctx                 (* Context eV : EV's bound in A/cG     *)
  ; cUVars : LF.mctx                 (* Context uV : UV's bound in [eV |- A :- cG] *)
  ; cSubGoals : conjunction          (* Subgoals cG                         *)
  }
  
  
module Shift : sig
  val shiftAtom : LF.typ -> int * int * int -> LF.typ
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

  let rec shiftTyp tM k =
    match tM with
    | LF.Atom (l, c, tS) ->
       LF.Atom (l, c, shiftSpine tS k)
    | x -> x

  and shiftSpine tS k =
    match tS with
    | LF.App (tN, tS) ->
       LF.App (shiftNormal tN k, shiftSpine tS k)
    | LF.SClo (tS, s) ->
       LF.SClo (shiftSpine tS k, s)
    | LF.Nil -> LF.Nil

  and shiftNormal tN k =
    match tN with
    | LF.Lam (l, n, tN') ->
       begin
         incr lR;
         let tM = LF.Lam (l, n, shiftNormal tN' k) in
         decr lR;
         tM
       end
    | LF.Root (l, tH, tS, plicity) ->
       LF.Root (l, shiftHead tH k, shiftSpine tS k, plicity)
    | LF.Clo (tN, s) ->
       LF.Clo (shiftNormal tN k, s)
    | LF.Tuple (l, tP) ->
       LF.Tuple (l, shiftTuple tP k)

  and shiftHead tH k =
    match tH with
    | LF.BVar i ->
       if i > !lR && i > !dR
       then LF.BVar (i + k)
       else if i > !lR && i <= !dR
       then LF.BVar (i + !dS)
       else LF.BVar i
    | LF.AnnH (tH, tM) ->
       LF.AnnH (shiftHead tH k, tM)
    | LF.Proj (tH, n) ->
       LF.Proj (shiftHead tH k, n)
    | x -> x

  and shiftTuple tP k =
    match tP with
    | LF.Last tN ->
       LF.Last (shiftNormal tN k)
    | LF.Cons (tN, tP') ->
       LF.Cons (shiftNormal tN k, shiftTuple tP' k)

  let shiftAtom tM (cS, dS', dR') =
    dR := dR';
    dS := dS';
    shiftTyp tM cS
end


module Convert = struct
  
  (* typToClause' eV cG M (cS, dS, dR) = clause
     Invariants:
       If BV(i) is free in M, then BV(i) is bound in (eV |- M).
       If M = PiTyp (x:A, No), then M ~ g.
  *)
  let rec typToClause' eV cG tM (cS, dS, dR) =
    match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
       typToClause' (LF.DDec (eV, tD)) cG tM' (cS, dS, dR)
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
       typToClause' eV (Conjunct (cG, typToGoal tA (cS, dS, dR)))
         tB (cS + 1, dS, dR)
    | LF.Atom _ ->
       { tHead = (Shift.shiftAtom tM (-cS, -dS, dR))
       ; eVars = eV
       ; subGoals = cG
       }

      
  (* comptypToCClause' cD U (cS, dS, dR) = cclause
     Invariants:
       If BV(i) is free in M, then BV(i) is bound in (eV |- M).
       If M = PiTyp (x:A, No), then M ~ g.
       If U = TypPiBox (u:t, U') then cD := cD, u:t

     TODO: arrow comp-typ to cclause
  *)
      
  and comptypToCClause' cD tM (cS, dS, dR) =
    match tM with
    | Comp.TypBox (l, LF.ClTyp (LF.MTyp typ, cPsi)) ->
       let tMclause = typToClause' cPsi True typ (cS, dS, dR) in 
       { ctHead = tMclause.tHead
       ; cEVars = tMclause.eVars
       ; cUVars = cD 
       ; cSubGoals = tMclause.subGoals
       }
    | Comp.TypPiBox (l, tdecl, tM') ->
       comptypToCClause' (Whnf.extend_mctx cD (tdecl, LF.MShift 0)) tM' (cS, dS, dR)
    
       
   

  (* Write out invariant / comment
     in particular: what is cS, dS, dR 
   *)       
  and typToGoal tA (cS, dS, dR) =
    match tA with
    | LF.PiTyp ((tdec, LF.Maybe), tA') ->
       All (tdec, typToGoal tA' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (x, tA) as tdec, LF.No), tB) ->
       Impl ((typToRes tA (cS, dS, dR), tdec), typToGoal tB (cS, dS, dR + 1))
    | LF.Atom _ ->
       Atom (Shift.shiftAtom tM (-cS, -dS, dR))

      
  and comptypToGoal tau (cS, dS, dR) =
    match tau with
    | Comp.TypBox (_loc, LF.ClTyp (LF.MTyp tA, cPsi)) ->
       (* Invariant: tA will always be atomic in our implementation *)
       Box (cPsi, Atom tA)
       (* possibly needs to have PiBox variables shifted;
          note: Pibox variables are indexed with respect to cD (Delta)
                LF Pi variables are indexed with respect to LF context 
                (hence one cannot simply re-use the module Shift, but would need a module MShift)
        *)
    | Comp.TypBox (_,_) ->
       raise NotImplementedYet
    | Comp.TypPiBox (loc, ctyp_decl , tau') ->
       Forall(ctyp_decl, comptypToCompGoal tau' )


  and typToRes tM (cS, dS, dR) =
    match tM with
    | LF.PiTyp ((tD, LF.Maybe), tM') ->
       Exists (tD, typToRes tM' (cS, dS, dR + 1))
    | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
       And (typToGoal tA (cS, dS, dR), typToRes tB (cS + 1, dS + 1, dR + 1))
    | LF.Atom _ ->
       Head (Shift.shiftAtom tM (-cS, -dS, dR))

  let rec resToClause' eV cG (r, s) =
    match r with
    | Exists (tD, r') ->
       resToClause' (LF.DDec (eV, tD)) cG (r', S.dot1 s)
    | And (g, r') ->
       resToClause' eV (Conjunct (cG, g)) (r', s)
    | Head tA ->
       let (tA', _) = Whnf.whnfTyp (tA, s) in
       { tHead = tA'; eVars = eV; subGoals = cG }

  let resToClause (r, s) =
    resToClause' LF.Null True (r, s)

  let typToClause tM =
    typToClause' LF.Null True tM (0, 0, 0)

  let comptypToCClause tM =
    comptypToCClause' LF.Empty tM (0, 0, 0)    

  (* etaExpand Psi (A, s) = normal
     Invariants:
       Psi |- s : Phi
       Phi |- A : LF.typ

     Effects:
       None.

    Example: tA = \x. X[x] : nat -> nat 
        meta-variable X generated by newMMVar at type nat in a context cPsi := x:nat
        (instead of a meta-variable of type nat -> nat)

  *)
  let rec etaExpand cD cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA in
    match tA with
    | LF.Atom _ ->
       let u = LF.Inst (Whnf.newMMVar None (cD, cPsi, LF.TClo (tA, s)) LF.Maybe) in
       LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil, `explicit)
    | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
       LF.Lam
         ( Syntax.Loc.ghost
         , x
         , etaExpand cD (LF.DDec (cPsi, S.decSub tD s)) (tB, S.dot1 s)
         )


      
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
  let rec dctxToSub cD cPsi (eV, s) fS =
    match eV with
    | LF.DDec (eV', LF.TypDecl (_, tM)) ->
       let (s', fS') = dctxToSub cD cPsi (eV', s) fS in
       let tM' = etaExpand cD cPsi (tM, s') in
       (LF.Dot (LF.Obj tM', s'), (fun tS -> fS' (LF.App (tM', tS))))
    | LF.Null -> (s, fS)
    | LF.CtxVar _ ->
       invalid_arg
         "Logic.Convert.dctxToSub: Match conflict with LF.CtxVar _."

  (** typToQuery (M, i)  = ((g, s), xs)
      Transform a reconstructed LF.typ into a query, accumulating all
      the abstracted existential variables into a substitution while
      storing the MVars into a list `xs' for immediate access.

      `i` is the count of abstracted existential variables in the
      type.
  *)
  let typToQuery cD cPsi (tA, i) =
    let rec typToQuery' (tA, i) s xs =
      match tA with
      | LF.PiTyp ((LF.TypDecl (x, tA), LF.Maybe), tB) when i > 0 ->
         let tN' = etaExpand cD cPsi (tA, s) in
         typToQuery' (tB, i - 1) (LF.Dot (LF.Obj tN', s)) ((x, tN') :: xs)
      | _ -> ((typToGoal tA (0, 0, 0), s), tA, s, xs)
    in
    typToQuery' (tA, i) S.id []

  let rec solToSub xs =
    match xs with
    | [] -> S.id
    | (x, tN) :: xs -> LF.Dot (LF.Obj tN, solToSub xs)

(*
  comptypToMQuery (tau,i) = comp_goal  

   Precondition:

     . |- tau : ctyp  (i.e. tau is a closed computation-level type)
          i  = # Pibox quantified variables in tau that denote existential variables, 
               i.e. we want to find instantiation for those variables during proof search.

   Postcondition (result)
      comp_goal is a the representation of the computation-level type tau as a computation-level goal


 *)
let comptypToMQuery (tau, i) =
  let rec comptypToMQuery' (tau, i) ms xs =
    (* 
     Invariant: 

       cD' |- tau 
       .   |- ms : cD'     ms is a meta-substitution that provides existential variables (refs that will instantiated) 
                              for all the bound meta-variables in cD'
       .   |- [ms]tau 

     *)
      match tau with
      | Comp.TypBox (_loc, LF.ClTyp (LF.MTyp _tA, _cPsi)) ->
         dprintf
         begin fun p ->
         p.fmt "goal = %a"
           (Pretty.Int.DefaultPrinter.fmt_ppr_cmp_typ LF.Empty Pretty.Int.DefaultPrinter.l0) (Whnf.cnormCTyp (tau,ms))
         end ; 
          ((comptypToCompGoal tau), tau, ms, xs) 
      | Comp.TypBox (_loc, LF.ClTyp (LF.PTyp _tA, _cPsi)) ->
         raise NotImplementedYet
      | Comp.TypBox (loc, LF.ClTyp (LF.STyp (_svar_c, _cPhi),  _cPsi)) ->
          raise NotImplementedYet
      | Comp.TypPiBox (loc, mdecl, tau)  when i > 0 ->
          let LF.Decl(x, mtyp, dep) = mdecl in  (* where mtyp = (LF.MTyp tA, cPsi) *)
          (* generate a meta-variable (instantiated by unification) of type (LF.MTyp tA, cPsi)
             and make sure it is an mfront *)
          let mmV = Whnf.newMMVar' (Some x) (LF.Empty, mtyp) dep in
          let mfront = Whnf.mmVarToMFront loc mmV mtyp in 
          comptypToMQuery' (tau , i-1) (LF.MDot (mfront, ms)) ((x, (loc, mfront)) :: xs)
      | Comp.TypPiBox (_,_, tau') when i = 0 ->
         dprintf
         begin fun p ->
         p.fmt "goal = %a"
           (Pretty.Int.DefaultPrinter.fmt_ppr_cmp_typ LF.Empty Pretty.Int.DefaultPrinter.l0) (Whnf.cnormCTyp (tau,ms))
         end ; 
         ((comptypToCompGoal tau), tau, ms, xs)
      | _ -> raise NotImplementedYet
    in
    comptypToMQuery' (tau, i) (LF.MShift 0) []

end

    
module Index = struct
  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  let compTypes = Hashtbl.create 0      (* compTypConst Hashtbl.t      *)

  type inst = (Id.name *  LF.normal)    (* I ::= (x, Y[s]) where Y is an MVar        *)
  type minst = (Id.name * LF.mfront)    (* I ::= (x, mf)   where mf is (Psihat.term) *)            
                                        (* where mf contains an MMVar *)
  type sgnQuery =
    { query : query                   (* Query ::= (g, s)            *)
    ; typ : LF.typ                    (* Query as LF.typ.            *)
    ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
    ; optName : Id.name option        (* Opt. name of proof term.    *)
    ; cD : LF.mctx                    (* Meta context.               *)
    ; expected : bound                (* Expected no. of solutions.  *)
    ; tries : bound                   (* No. of tries to find soln.  *)
    ; instMVars : inst list           (* MVar instantiations.        *)
    }

  type sgnMQuery =
    { mquery : mquery                 (* MQuery ::= (c_g, ms)        *)
    ; skinnyCompTyp : Comp.typ        (* MQuery stripped of E-vars.  *)
    ; mexpected : bound               (* Expected no. of solutions.  *)
    ; mtries : bound
    ; depth : bound                  (* No. of tries to find soln.  *)
    ; instMMVars : minst list         (* MMVar instantiations.       *)
    }
    

  let queries = DynArray.create ()      (* sgnQuery DynArray.t         *)
  let mqueries = DynArray.create ()     (* sgnMQuery DynArray.t        *)              

  let querySub = ref S.id

  (* addTyp c = sgnClause DynArray.t
     Create a new entry for a type constant, c, in the `types' table and
     return its mapping, i.e. an empty DynArray.
  *)
  let addTyp cidTyp =
    Hashtbl.add types cidTyp (DynArray.create ());
    Hashtbl.find types cidTyp

  (* addCompTyp c = sgnCClause DynArray.t
     Create new entry for a compTyp constant c in the `compTypes' table
     and return its mapping 
  *)
    
  let addCompTyp cidTyp =
    Hashtbl.add compTypes cidTyp (DynArray.create ());
    Hashtbl.find compTypes cidTyp

  (* addSgnClause tC, sCl = ()
     Add a new sgnClause, sCl, to the DynArray tC.
  *)
  let addSgnClause typConst sgnClause =
    DynArray.add typConst sgnClause
    
(* TODO:: create new DynArray for compclauses
   addSgnClause tC, sCCl = ()
     Add a new sgnClause, sCl, to the DynArray tC.
  *)
  let addSgnCClause typConst sgnCClause =
    DynArray.add typConst sgnCClause
 
  (* addSgnQuery (p, (g, s), cD, xs, e, t)  = ()
     Add a new sgnQuery to the `queries' DynArray.
  *)
  let addSgnQuery (p, a, a', q, cD, xs, e, t) =
    DynArray.add queries
      { query = q
      ; typ = a
      ; skinnyTyp = a'
      ; optName = p
      ; cD = cD 
      ; expected = e
      ; tries = t
      ; instMVars = xs
      }

    
  (* addSgnMQuery (tau', ttau, xs, e, t)  = ()
     Add a new sgnMQuery to the `mqueries' DynArray.
   *)
  let addSgnMQuery (tau', mq, xs, e, t, d) =
    DynArray.add mqueries
      { mquery = mq
      ; skinnyCompTyp = tau'
      ; mexpected = e
      ; mtries = t
      ; depth = d
      ; instMMVars = xs
      }    
    
  (* compileSgnClause c = (c, sCl)
     Retrieve LF.typ for term constant c, clausify it into sCl and
     return an sgnClause (c, sCl).
  *)
  let compileSgnClause cidTerm =
    let termEntry = Cid.Term.get cidTerm in
    let tM = termEntry.Cid.Term.Entry.typ in
    (cidTerm, Convert.typToClause tM)


    
  (* compileSgnCClause c = (c, sCCl)
     Retrieve Comp.typ for term constant c, clausify it into sCCl and
     return an sgnCClause (c, sCCl). 
   *)

  let compileSgnCClause cidTerm =
    let termEntry = Cid.Comp.get cidTerm in
    let tM = termEntry.Cid.Comp.Entry.typ in
    (cidTerm, Convert.comptypToCClause tM)

    

  (* termName c = Id.name
     Get the string representation of term constant c.
  *)
  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.Entry.name

  let compTermName cidTerm =
    (Cid.Comp.get cidTerm).Cid.Comp.Entry.name

  (* storeTypConst c = ()
     Add a new entry in `types' for type constant c and fill the DynArray
     with the clauses corresponding to the term constants associated with c.
     The revIter function serves to preserve the order of term constants
     intrinsic to the Beluga source file, since the constructors for c are
     listed in reverse order.
  *)
  let storeTypConst (cidTyp, typEntry) =
    let typConstr = !(typEntry.Cid.Typ.Entry.constructors) in
    let typConst = addTyp cidTyp in
    let regSgnClause cidTerm =
      (*  try  *) 
        addSgnClause typConst (compileSgnClause cidTerm)
    (*  with failure ->
        addSgnClause typConst (compileSgnCClause cidTerm) *)
    in
    let rec revIter f =
      function
      | [] -> ()
      | h :: l' ->
         revIter f l';
         f h
    in
    revIter regSgnClause typConstr

  (* storeCompTypConst c = ()
     Add a new entry in `Comptypes' for comptype constant c and fill the 
     DynArray with the clauses corresponding to the term constants associated 
     with c.
   *)
    
  let storeCompTypConst (cidTyp, typEntry) =
    let typConstr = !(typEntry.Cid.Typ.Entry.constructors) in  
    let typConst = addCompTyp cidTyp in
    let regSgnCClause cidTerm =
      addSgnCClause typConst (compileSgnCClause cidTyp)
    (*  with failure ->
        addSgnClause typConst (compileSgnCClause cidTerm) *)
    in
    let rec revIter f =
      function
      | [] -> ()
      | h :: l' ->
         revIter f l';
         f h
    in
    revIter regSgnCClause typConstr 

  (* storeQuery (p, (tA, i), cD, e, t) = ()
     Invariants:
       i = # of abstracted EVars in tA
  *)
  let storeQuery (p, (tA, i), cD,  e, t) =
    let (q, tA', s, xs) = (Convert.typToQuery LF.Empty LF.Null (tA, i)) in
    querySub := s;
    addSgnQuery (p, tA, tA', q, cD, xs, e, t)


  (* storeMQuery ((tau, i), e, t) = ()
     Invariants:
       i = # of abstracted EVars in tA
       e = expected number of  solutions
       t = expected number of tries to find soln.
  *)
  let storeMQuery ((tau, i), e, t, d) =
    (*  TO BE IMPLEMENTED AND FINISHED *)
    let (comp_goal, tau', ms, xs) = (Convert.comptypToMQuery (tau, i)) in
    let mq = (comp_goal, ms) in
    addSgnMQuery (tau', mq, [], e, t, d)


    
  (* robStore () = ()
     Store all type constants in the `types' table.
  *)
  let robStore () =
    try
      List.iter storeTypConst (Cid.Typ.current_entries ())
    with
    | _ -> ()

  (* robSecondStore () = ()
     Store all comptype constants in the `compTypes' table.

 TODO:: current_entries for compTyps???
  *)
  let robSecondStore () =
    try
      List.iter storeCompTypConst (Cid.Typ.current_entries ())
    with
    | _ -> ()

  (* iterSClauses f c = ()
     Iterate over all signature clauses associated with c.
  *)
  let iterSClauses f cidTyp =
    DynArray.iter f (Hashtbl.find types cidTyp)

  let iterAllSClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) types

  let iterSCClauses f cidTyp =
    DynArray.iter f (Hashtbl.find compTypes cidTyp)

  let iterAllSCClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) compTypes

  let iterQueries f =
    DynArray.iter (fun q -> f q) queries

  let iterMQueries f =
    DynArray.iter (fun q -> f q) mqueries
  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () =
    DynArray.clear queries;
    Hashtbl.clear types


  let singleQuery (p, (tA, i), cD, e, t) f =
    let (q, tA', s, xs) = (Convert.typToQuery LF.Empty LF.Null (tA, i)) in
    querySub := s;
    robStore ();
    robSecondStore ();
    let bchatter = !Options.chatter in
    Options.chatter := 0;
    let sgnQ =
      { query = q
      ; typ = tA
      ; skinnyTyp = tA'
      ; optName = p
      ; cD = cD
      ; expected = e
      ; tries = t
      ; instMVars = xs
      }
    in
    f sgnQ;
    Options.chatter := bchatter;
    Hashtbl.clear types;
    Hashtbl.clear compTypes
end



module Printer = struct
  module P = Pretty.Int.DefaultPrinter
  open Index

  let fmt_ppr_dctx cD ppf  cPsi =
    P.fmt_ppr_lf_dctx cD P.l0 ppf cPsi

  let fmt_ppr_typ cD cPsi ppf sA =
    P.fmt_ppr_lf_typ cD cPsi P.l0 ppf (Whnf.normTyp sA)

  let fmt_ppr_cmp_typ cD ppf sA =
    P.fmt_ppr_cmp_typ cD P.l0 ppf sA

  let fmt_ppr_normal cD cPsi ppf sM =
    P.fmt_ppr_lf_normal cD cPsi P.l0 ppf (Whnf.norm sM)

  let fmt_ppr_decl cD cPsi ppf (tD, s) =
    match tD with
    | LF.TypDeclOpt x ->
       fprintf ppf "%a : _"
         Id.print x
    | LF.TypDecl (x, tA) ->
       fprintf ppf "%a : %a"
         Id.print x
         (fmt_ppr_typ cD cPsi) (tA, s)

  (* goalToString Psi (g, s) = string
     Invariants:
       Psi |- s : Phi
       Phi |- g : goal
       Psi |- g[s] : goal

     Effects:
       None.
  *)
  let rec fmt_ppr_goal cD cPsi ppf (g, s) =
    match g with
    | Atom tA ->
       fmt_ppr_typ cD cPsi ppf (tA, s)
    | Impl ((r, tD), g') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_res cD cPsi) (r, s)
         (fmt_ppr_goal cD (LF.DDec (cPsi, S.decSub tD s))) (g', S.dot1 s)
    | All (tD, g') ->
       fprintf ppf "[∀%a. %a]"
         (fmt_ppr_decl cD cPsi) (tD, s)
         (fmt_ppr_goal cD (LF.DDec (cPsi, S.decSub tD s))) (g', S.dot1 s)

  (* resToString cPsi (r, s) = string
     Invariants:
       Psi |- s: Phi
       Phi |- r : res
       Psi |- r[s] : res

     Effects:
       None.
  *)
  and fmt_ppr_res cD cPsi ppf (r, s) =
    match r with
    | Head tH ->
       fmt_ppr_typ cD cPsi ppf (tH, s)
    | And (g, r') ->
       fprintf ppf "%a -> %a"
         (fmt_ppr_goal cD cPsi) (g, s)
         (fmt_ppr_res cD cPsi) (r', s)
    | Exists (LF.TypDecl (_, _tA) as tD, r') ->
       fprintf ppf "[∃%a. %a]"
         (fmt_ppr_decl cD cPsi) (tD, s)
         (fmt_ppr_res cD (LF.DDec (cPsi, S.decSub tD s))) (r', S.dot1 s)

  (** Prints each subgoal with a leading `<-`. *)
  let fmt_ppr_subgoals cD cPsi ppf (cG, s) =
    fprintf ppf "@[<v>%a@]"
      (pp_print_list ~pp_sep: pp_print_cut
         (fun ppf g ->
           fprintf ppf "<- %a"
             (fmt_ppr_goal cD cPsi) (g, s)))
      (list_of_conjunction cG)

  (* sgnClauseToString (c, sCl) = string
     String representation of signature clause.
  *)
  let fmt_ppr_sgn_clause ppf (cidTerm, sCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Id.print (termName cidTerm)
      (fmt_ppr_typ LF.Empty sCl.eVars) (sCl.tHead, S.id)
      (fmt_ppr_subgoals LF.Empty sCl.eVars) (sCl.subGoals, S.id)

  let fmt_ppr_sgn_cclause ppf (cidTerm, sCCl) =
    fprintf ppf "@[<v 2>@[%a@] : @[%a@]@,%a@]"
      Id.print (compTermName cidTerm)
      (fmt_ppr_typ LF.Empty sCCl.cEVars) (sCCl.ctHead, S.id) 
      (fmt_ppr_subgoals LF.Empty sCCl.cEVars) (sCCl.cSubGoals, S.id)

  let fmt_ppr_bound ppf =
    function
    | Some i -> fprintf ppf "%d" i
    | None -> fprintf ppf "*"

  let fmt_ppr_sgn_query ppf q =
    fprintf ppf "--query %a %a %a."
      fmt_ppr_bound q.expected
      fmt_ppr_bound q.tries
      (fmt_ppr_typ LF.Empty LF.Null) (q.typ, S.id)

  let fmt_ppr_sgn_mquery ppf mq =
      fprintf ppf "--mquery %a %a %a %a."
        fmt_ppr_bound mq.mexpected
        fmt_ppr_bound mq.mtries
        fmt_ppr_bound mq.depth
        (fmt_ppr_cmp_typ LF.Empty) mq.skinnyCompTyp

  (* instToString xs = string
     Return string representation of existential variable
     instantiations in the query.
   *)
  let fmt_ppr_inst ppf =
    function
    | [] -> fprintf ppf "^."
    | xs ->
       fprintf ppf "@[<v>%a@]."
         (pp_print_list ~pp_sep: pp_print_cut
            (fun ppf (x, tA) ->
              fprintf ppf "%a = %a;"
                Id.print x
                (fmt_ppr_normal LF.Empty LF.Null) (tA, S.id)))
         xs

  let printQuery q =
    fprintf std_formatter "%a.@.@."
      fmt_ppr_sgn_query q

  let printMQuery mq =
    fprintf std_formatter "%a.@.@."
      fmt_ppr_sgn_mquery mq  

  let printSignature () =
    iterAllSClauses
      (fun w ->
        fprintf std_formatter "%a@."
          fmt_ppr_sgn_clause w)

  let printCompSignature () =
    iterAllSCClauses
      (fun w ->
        fprintf std_formatter "%a@."
          fmt_ppr_sgn_cclause w)
end

module Solver = struct
  module P = Printer.P
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
    U.unifyTyp cD cPsi sA sB;
    sc ()

  (* trail f = ()
     Trail a function. If an exception is raised, unwind the trail and
     propagate the exception.
  *)
  let trail f =
    U.mark ();
    try
      f ();
      U.unwind ()
    with
    | e ->
       U.unwind ();
       raise e

  (* eqHead A dCl = bool
     Compare the cid_typ's of A and the head of dCl.
  *)
  let eqHead tA dCl =
    match (tA, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) -> Id.cid_equals i j
    | _ -> false

  (* cidFromAtom A = cid_typ *)
  let cidFromAtom =
    function
    | LF.Atom (_, i, _) -> i
    | _ ->
       invalid_arg
         "Logic.Solver.cidFromAtom: Match failure against LF.Atom (_, _, _)."

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
  let rec gSolve dPool cD (cPsi, k) (g, s) sc =
    match g with
    | Atom tA ->
       matchAtom dPool cD (cPsi, k) (tA, s) sc

    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
       (* extend the dynamic pool with the new assumption and prove the conclusion *)
       let dPool' =
         DynCl (dPool, (C.resToClause (r, s), k))
       in
       gSolve dPool' cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

    | All (LF.TypDecl (x, _) as tD, g') ->
       (* we *don't* get an assumption from a forall; it's just a parameter.
          So we just prove the conclusion in an extended context. *)
       gSolve dPool cD (LF.DDec (cPsi, S.decSub tD s), k + 1) (g', S.dot1 s)
         (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

  (* matchAtom dPool Delta (Psi, k) (A, s) sc = ()
     Invariants:
       dPool ~ Psi, k = |Psi|
       Delta; Psi |- s : Phi
       Delta; Phi |- A : Atom
       sc : proof -> unit
       If Delta; Psi |- M : A[s], then (sc M) is evaluated.

     Effects:
       Instatiation of MVars in s and dPool.
       Any effect (sc M) might have.
  *)
  and matchAtom dPool cD (cPsi, k) (tA, s) sc =
    (* some shorthands for creating syntax *)
    let root x = LF.Root (Syntax.Loc.ghost, x, LF.Nil, `explicit) in
    let pvar k = LF.PVar (k, LF.Shift 0) in
    let mvar k = LF.MVar (LF.Offset k, LF.Shift 0) in
    let proj x k = LF.Proj (x, k) in

    (* matchDProg dPool = ()
       Try all the dynamic clauses in dPool starting with the most
       recent one. If dPool is empty, try the signature.
    *)
    let rec matchDProg =
      function
      | DynCl (dPool', (dCl, k')) ->
         if (eqHead tA dCl)
         then
           begin
             let (s', fS) =
               C.dctxToSub cD cPsi (dCl.eVars, shiftSub (k - k'))
                 (fun tS -> tS) in
             (* Trail to undo MVar instantiations. *)
             try
               trail
                 begin fun () ->
                 unify cD cPsi (tA, s) (dCl.tHead, s')
                   begin fun () ->
                   solveSubGoals dPool cD (cPsi, k) (dCl.subGoals, s')
                     begin fun (u, tS) ->
                     let tM =
                       LF.Root
                         ( Syntax.Loc.ghost
                         , LF.BVar (k - k')
                         , fS (spineFromRevList tS)
                         , `explicit
                         )
                     in
                     sc (u, tM)
                     end
                   end
                 end
             with
             | U.Failure _ -> ()
           end;
         matchDProg dPool'

      | Empty ->
         try 
           matchSig (cidFromAtom tA)
         with failure ->
           matchCompSig (cidFromAtom tA)

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
    and matchSigma (pv : LF.head) (cD : LF.mctx) (psi : LF.dctx) (tRec : LF.typ_rec) sc : unit =
      let rec loop (typs, ts) k =
        let check typ =
          try
            trail
              begin fun () ->
              U.unifyTyp cD psi (typ, ts) (tA, s);
              dprintf
                begin fun p ->
                p.fmt "[logic] [matchSigma] \
                       @[<v>Found solution with projection %d of sigma-type:\
                       @,@[%a@]@]"
                  k
                  (P.fmt_ppr_lf_typ_rec cD psi P.l0) tRec
                end;
              sc k
              end
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
           loop
             (typs, LF.Dot (LF.Head (proj pv k), ts))
             (k + 1)
      in
      loop (tRec, LF.Shift 0) 1

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
     and matchDelta (cD' : LF.mctx) =
      let rec loop cD' k =
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
                    matchSigma (pvar k) cD psi' typs
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
                    dprintf
                      begin fun p ->
                      p.fmt "[logic] [matchDelta] found solution: variable %d" k
                      end;

                    (* We need to create the syntax to refer to this _meta_ variable *)
                    sc (psi', root (mvar k))

                 | LF.STyp _ ->
                    (* ignore substitution variables for now *)
                    ()
                 end
             with
             | U.Failure s -> ()
           end;
           loop cD' (k + 1)
      in
      loop cD' 1

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
     *)
    and matchSig cidTyp =
      I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (*    TODO:: where to use matchCompSig???   *)
    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
     *)
    and matchCompSig cidTyp =
      I.iterSCClauses (fun w -> matchSgnCClause w sc) cidTyp  

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the head of sCl with A[s]. If unification succeeds,
       attempt to solve the subgoals of sCl.
     *)
    and matchSgnClause (cidTerm, sCl) sc =
      let (s', fS) =
        C.dctxToSub cD cPsi (sCl.eVars, shiftSub (Context.dctxLength cPsi))
          (fun tS -> tS)
      in
      (* Trail to undo MVar instantiations. *)
      try
        trail
          begin fun () ->
          U.unifyTyp cD cPsi (tA, s) (sCl.tHead, s');
          solveSubGoals dPool cD (cPsi, k) (sCl.subGoals, s')
            begin fun (u, tS) ->
            let tM =
              LF.Root
                ( Syntax.Loc.ghost
                , LF.Const (cidTerm)
                , fS (spineFromRevList tS)
                , `explicit
                )
            in
            sc (u, tM)
            end
          end
      with
      | U.Failure _ -> ()
                     
    and matchSgnCClause (cidTerm, sCCl) sc =
      let (s', fS) =
        C.dctxToSub cD cPsi (sCCl.cEVars, shiftSub (Context.dctxLength cPsi))
          (fun tS -> tS)
      in
      (* Trail to undo MVar instantiations. *)
      try
        trail
          begin fun () ->
          U.unifyTyp cD cPsi (tA, s) (sCCl.ctHead, s');
          solveSubGoals dPool cD (cPsi, k) (sCCl.cSubGoals, s')
            begin fun (u, tS) ->
            let tM =
              LF.Root
                ( Syntax.Loc.ghost
                , LF.Const (cidTerm)
                , fS (spineFromRevList tS)
                , `explicit
                )
            in
            sc (u, tM)
            end
          end
      with
      | U.Failure _ -> ()
    in
    (* ^ end of the gigantic let of all the helpers for matchAtom;
     * Now here's the actual body of matchAtom: *)
    matchDelta cD

  (* spineFromRevList : LF.normal list -> LF.spine
     build an LF.spine out of a list of LF.normal, reversing the order of the elements*)
  and spineFromRevList lS =
    List.fold_left (fun tSc tMc -> LF.App (tMc, tSc)) LF.Nil lS

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
  and solveSubGoals dPool cD (cPsi, k) (cG, s) sc =
    match cG with
    | True -> sc (cPsi, [])
    | Conjunct (cG', g) ->
       gSolve dPool cD (cPsi, k) (g, s)
         begin fun (u, tM) ->
         solveSubGoals dPool cD (cPsi, k) (cG', s)
           begin fun (v, tS) ->
           sc (v, tM :: tS)
           end
         end

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
  (* exception DepthReached of bound                (* Stops a query going beyond the specified depth *) *)

  (* exceeds B1 B2 = b
     True if B1 = * or B1 >= B2.
  *)
  let exceeds x y =
    match (x, y) with
    | (Some i, Some j) -> i >= j
    | (Some i, None) -> false
    | (None, _) -> true

  (* boundEq B1 B2 = b
     Equality function for bounds.
  *)
  let boundEq x y = Option.equal (=) x y

  (* lowerBound B1 B2 = min (B1, B2) *)
  let lowerBound x y =
    match (x, y) with
    | (Some i, Some j) -> Some (min i j)
    | (x, None) -> x
    | (None, y) -> y

  (* Abort query. *)
  let abort f =
    let s =
      f str_formatter ();
      flush_str_formatter ()
    in
    raise (AbortQuery s)

  (* checkSolutions e t s = () *)
  let checkSolutions e t s =
    match (e, t) with
    | (None, None) -> ()
    | _ ->
       if not (boundEq (lowerBound e t) (Some s))
       then
         abort
           begin fun ppf () ->
           fprintf ppf
             "Query error: Wrong number of solutions -- \
              expected %a in %a tries, but found %d"
             P.fmt_ppr_bound e
             P.fmt_ppr_bound t
             s
           end

  (* moreSolutions () = () *)
  let moreSolutions () =
    printf "More? ";
    match read_line () with
    | "y" | "Y" | ";" -> true
    | "q" | "Q" ->
       abort (fun ppf () -> fprintf ppf "Query error -- explicit quit.")
    | _ -> false

  (* solve q = () *)
  let solve sgnQuery =

    (* Keep track of no. of solutions found. *)
    let solutions = ref 0 in

    (* Type checking function. *)
    let check cPsi tM s =
      Check.LF.check LF.Empty
        cPsi (tM, S.id) (sgnQuery.skinnyTyp, s)
    in


    (* Initial success continuation. *)
    let scInit (cPsi, tM) =
      incr solutions;

      (* Rebuild the substitution and type check the proof term. *)
      if !Options.checkProofs
      then check cPsi tM (Convert.solToSub sgnQuery.instMVars); (* !querySub *)

      (* Print MVar instantiations. *)
      if !Options.chatter >= 3
      then
        begin
          fprintf std_formatter "@[<v>---------- Solution %d ----------@,[%a]@,%a@,@]"
            (!solutions)
            (P.fmt_ppr_dctx LF.Empty) cPsi
            P.fmt_ppr_inst sgnQuery.instMVars;
          (* Print proof term. *)
          begin match sgnQuery.optName with
          | Some n ->
             fprintf std_formatter "%a@."
               P.fmt_ppr_inst [(n, tM)]
          | None -> ()
          end;
          fprintf std_formatter "@."
        end;
      (* Interactive. *)
      if !Options.askSolution && not (moreSolutions ())
      then raise Done;

      (* Stop when no. of solutions exceeds tries. *)
      if exceeds (Some !solutions) sgnQuery.tries
      then raise Done
    in

    if not (boundEq sgnQuery.tries (Some 0))
    then
      begin
        if !Options.chatter >= 1
        then P.printQuery sgnQuery;
        try
          Solver.solve sgnQuery.cD LF.Null sgnQuery.query scInit;
          (* Check solution bounds. *)
          checkSolutions sgnQuery.expected sgnQuery.tries !solutions
        with
        | Done -> printf "Done.\n"
        | AbortQuery s -> printf "%s\n" s
        | _ -> ()
      end
    else if !Options.chatter >= 2
    then printf "Skipping query -- bound for tries = 0.\n"


  let msolve sgnMQuery =
    (*  unroll cD  (cg,ms) = (cD', cg_atomic) 

       if         

        cD |- [ms]cg      computation-level goal cg is well-formed/well-typed 
                          in the meta-context cD where 
        cD' |- cg        
        cD  |- ms : cD'                               
            |- cD mctx    (cD is a well-formed meta-context)
      
       then 
   
         cg_atomic is either a Boxed Type or an Inductive Type 
         cD' |- cg_atomic  (computation-level goal cg is well-formed/well-typed 
                            in the meta-context cD) 
         |- cD' mctx       (cD' is a well-formed meta-context)
         cD' is an extension of cD

     *)    
    let rec unroll cD (cg,ms) = match (cg,ms) with
      | (Box (_cPsi, _g), ms) -> (cD, (cg,ms))
      | (Forall (tdecl, cg'), ms) ->
          unroll (Whnf.extend_mctx cD  (tdecl,ms)) (cg',Whnf.mvar_dot1 ms) 
    in 
    let solutions = ref 0 in
    let (cD, mgoal_atomic) = unroll LF.Empty sgnMQuery.mquery in  
    match mgoal_atomic  with
    | (Box(cPsi, g) , ms) ->
       let scInit (cPsi, tM) =
          incr solutions;
          begin
            fprintf std_formatter  "@[<v>---------- Solution %d ----------@,[%a |- %a]@]" 
              (*              "@[<hov 2>@[%a@] |-@ @[%a@]@]" *)
              (!solutions)
              (P.fmt_ppr_dctx cD) cPsi
              (P.fmt_ppr_normal cD cPsi) (tM, Substitution.LF.id);    
            
            fprintf std_formatter "@.@.";
            
            (* Stop when no. of solutions exceeds tries. *)
            if exceeds (Some !solutions) sgnMQuery.mtries   
            then raise Done;

            (* Temporary: Exiting as soon as we receive as many solutions as required *)
            if exceeds (Some !solutions) sgnMQuery.mexpected   
            then raise Done;
          end 
       in
        if not (boundEq sgnMQuery.mtries (Some 0))
        then
          begin
            if !Options.chatter >= 1
              then P.printMQuery sgnMQuery;
            try
                Solver.solve cD cPsi (g, Substitution.LF.id) scInit;
                (* Check solution bounds. *)
                checkSolutions sgnMQuery.mexpected sgnMQuery.mtries !solutions
              with
              | Done -> printf "Done.\n"
              | AbortQuery s -> printf "%s\n" s
              (* | DepthReached d -> printf "Query complete -- depth = %a was reached\n" P.fmt_ppr_bound d *)
              | _ -> ()
          end
        else if !Options.chatter >= 2
        then printf "Skipping query -- bound for tries = 0.\n";
        
    | _ -> (* since we only consider atomic goals here the other option is an inductive type 
              which is not yet in our comp_goal data type and we do not yet solve / search for 
              such goals
            *) 
       raise NotImplementedYet 
end

(* Interface *)

let storeQuery p (tA, i) cD e t =
  Index.storeQuery (p, (tA, i), cD, e, t)

let storeMQuery  (tau, i) e t d =
  Index.storeMQuery ((tau, i), e, t, d)

  
(* runLogic () = ()
   If !enabledLogic, run the logic programming engine. Otherwise
   do nothing, i.e. return unit.
*)
let runLogic () =
  if !Options.enableLogic
  then
    begin
      (* Transform LF signature into clauses. *)
      Index.robStore ();
      (* Transform Comp signatures into clauses. *)
      Index.robSecondStore ();
      (* Optional: Print signature clauses. *)
      if !Options.chatter >= 4
      then (Printer.printSignature ();
            Printer.printCompSignature ());
      (* Solve! *)
      Index.iterQueries Frontend.solve;
      Index.iterMQueries Frontend.msolve;      
      (* Clear the local storage.  *)
      Index.clearIndex ()
    end


let runLogicOn n (tA, i) cD e t  =
  Index.singleQuery (n, (tA, i), cD, e, t) Frontend.solve

let prepare () =
  Index.clearIndex ();
  Index.robStore ();
  Index.robSecondStore ()

(*


let runLogicOn n (cD, cPsi, tA, i) e t  =
  Index.singleQuery (n, (tA, i), e, t) Frontend.solve
 *)
