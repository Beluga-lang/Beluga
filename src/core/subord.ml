(**
   Printing the subordination relation.
   Computing the relation is done in store.ml, as constructors are added.
   Also has `thin', which uses subordination to generate a substitution that
    doesn't use irrelevant parts of a context.

   @author Joshua Dunfield
*)

include Options.Subord

open Support
open Syntax.Int.LF
module Types = Store.Cid.Typ
module Schema = Store.Cid.Schema

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [28]))
open Debug.Fmt

(*
 * OVERVIEW
 *
 * The type B is subordinate to the type A if a term of type A can appear in a term of type B.
 * Subordination is entirely a data-level (LF) notion; it can be determined from the
 * LF signature alone.
 *
 * The usual reference for subordination is Roberto Virga's 1999 thesis.  However, Virga
 *  does not call it subordination; rather, he uses a "dependence relation" (pp. 55-59),
 *  also called "containment".
 *
 * The following statements are equivalent:
 *    "h-terms can contain g-terms"
 *    "h is subordinate to g"
 *    "g subordinates h"
 *
 * In addition, we define---separately from the "h-terms can contain g-terms"
 * relation---a _type subordination_ relation that says whether a type can contain
 * terms of another type.  For example, in the usual dependent indexing of lists by
 * their length, we have
 *
 *     list : nat -> type.
 *
 * Therefore "list-terms can contain nat-terms", or equivalently,
 *
 *   "list is type-subordinate to nat"
 *   "nat type-subordinates list"
 *
 * Note that while term-level subordination is transitive---if terms of type k can
 * include terms of type h, and terms of type h can include terms of type g, then
 * terms of type k can include terms of type g---type-level subordination is *not*
 * a transitive relation.
 *
 *     list : nat -> type.
 *     t : list (suc (suc z)) -> type.
 *
 * t is type-subordinate to list, and list is type-subordinate to nat, but t is *not*
 * type-subordinate to nat, because the dependent type arguments to t does not
 * include nat-terms.
 *
 * -jd 2010-06
 * [BP : NOTE 5 Apr, 2011 ]
 *     list : nat -> type.
 *     t : list (suc (suc N)) -> type.
 *
 * t is type-subordinate to list, and list is type-subordinate to nat; t *must*
 * be type-subordinate to nat, because the dependent type arguments to t does
 * include nat-terms.
 *)


(*  relevant tA basis = rlist

    For every type family occurring in tA,
    check if it is a subordinate of a type in basis
          or it is equal to a type in basis;

    Idea : Can tA be used to construct elements in basis ?
      if there is a type family a in tA s.t. a is a
      subordinate of a type in basis or a itself is equal to
      a type in basis,  then we will keep a.

      Elements of the type family a can be used to construct
      elements in basis
*)
let rec relevant tA basis =
  match tA with
  | Atom (_, a, _) ->
     Types.freeze a;
     if List.exists
          begin fun type_in_basis ->
          Types.is_subordinate_to type_in_basis a
          || Id.cid_equals a type_in_basis
          end basis
     then [a]
     else []
  | PiTyp ((TypDecl (_, tA1), _), tA2) ->
     (* extract_pos returns all types which are in a positive position *)
     let rec extract_pos =
       function
       | Atom _ -> [tA]
       | PiTyp ((TypDecl (_, tA1), _), tA2) ->
          extract_neg tA1 @ extract_pos tA2
     and extract_neg =
       function
       | Atom _ -> []
       | PiTyp ((TypDecl (_, tA1), _), tA2) ->
          extract_pos tA1 @ extract_neg tA2
     in
     (* (relevant tA1 basis) @
        If we keep this, then we might not strengthen enough... -bp*)
     List.fold_left (fun l tA -> relevant tA basis @ l) [] (extract_neg tA1)
     @ relevant tA2 basis
  | Sigma typRec -> relevantTypRec typRec basis

and relevantTypRec tRec basis =
  match tRec with
  | SigmaLast (_, tA) -> relevant tA basis
  | SigmaElem (_, tA, typRec) ->
     relevant tA  basis @ relevantTypRec typRec basis

and relevantSchema (Schema sch_elems) basis =
  List.exists
    begin fun (SchElem (_, typRec)) ->
    List.nonempty (relevantTypRec typRec basis)
    end
    sch_elems

(* thin (cO, cD) (tP, cPsi) = (s, cPsi')

   if  cO ; cD |- cPsi ctx
       cO ; cD ; cPsi |- tP <= type
   then
       cO ; cD |- cPsi' ctx
       cO ; cD; cPsi |- s : cPsi'
       cO ; cPsi'    |- [s]^1(tP) : type

  Informally: we throw out any declaration from cPsi, which is irrelevant to
    construct objects of type tP; i.e. cPsi' is the strengthened cPs.

    s    is a weakening substitution
    s^1  is a strengthening substitution
 *)
let thin cD (tP, cPsi) =
  (*inner basis cPsi = (s, cPsi')

     if basis is a list of type families
        cD |- cPsi ctx
     then
        cPsi' only contains those declarations whose types is
        relevant to constructing elements of type families
        in basis.

     Initially, basis is `b' where tP = Atom (_, b, _).
   *)
  let rec inner (basis : Id.cid_typ list) cPsi =
    match cPsi with
    | Null -> (Shift 0, Null) (* . |- shift(noCtx, 0) : . *)
    | CtxVar psi ->
       let schema =
         match psi with
         | CtxOffset _ -> Context.lookupCtxVarSchema cD psi
         | CInst ({ typ = CTyp (Some cid_schema); _ }, _) -> cid_schema
       in
       if relevantSchema (Schema.get_schema schema) basis
       then
         begin
           (*print_string "Keeping context variable\n"; *)
           (Shift 0, CtxVar psi) (* psi |- shift(noCtx, 0) : psi *)
         end
       else
         begin
           (* print_string ("Denying that the context variable is relevant to anything in " ^ basisToString basis ^ "\n"); *)
           (EmptySub (*Shift (CtxShift psi, 0) *), Null) (* psi |- shift(noCtx, 0) : . *)
         end
    | DDec (cPsi, TypDecl (name, tA)) ->
       begin match relevant (Whnf.normTyp (tA, Substitution.LF.id)) basis with
       | [] ->
          let (thin_s, cPsi') = inner basis cPsi in
          (* cPsi |- thin_s : cPsi' *)
          (Substitution.LF.comp thin_s (Shift 1), cPsi')
       (* cPsi, x:tA |- thin_s ^ 1 : cPsi' *)
       | nonempty_list ->
          let (thin_s, cPsi') = inner (nonempty_list @ basis) cPsi in
          (* cPsi |- thin_s <= cPsi' *)
          (* cPsi,x:tA |- dot1 thin_s <= cPsi', x:tA'  where tA = [thin_s]([thin_s_inv]tA) *)
          let thin_s_inv = Substitution.LF.invert thin_s in
          (Substitution.LF.dot1 thin_s, DDec (cPsi', TypDecl (name, TClo (tA, thin_s_inv))))
       end
  in
  inner (match tP with Atom (_, a, _) -> [a]) cPsi

exception NoSchema
let thin0 cD a cPsi =
  (*inner basis cPsi = (s, cPsi')

     if basis is a list of type families
         cD |- cPsi ctx
     then
        cPsi' only contains those declarations whose types is
        relevant to constructing elements of type families
        in basis.

     Initially, basis is `b' where tP = Atom (_, b, _).
   *)
  let rec inner (basis : Id.cid_typ list) cPsi =
    match Whnf.cnormDCtx (cPsi, MShift 0) with
    | Null -> (Shift 0, Null) (* . |- shift(noCtx, 0) : . *)
    | CtxVar psi ->
       begin
         try
           let schema =
             match psi with
             | CtxOffset _ -> Context.lookupCtxVarSchema cD psi
             | CInst ({ typ = CTyp (Some cid_schema); _ }, _) -> cid_schema
             | CtxName psi ->
                let (_, Decl (_, CTyp (Some s_cid), _)) = Store.FCVar.get psi in
                s_cid
             | _ -> raise NoSchema
           in
           if relevantSchema (Schema.get_schema schema) basis
           then (Shift 0, CtxVar psi) (* psi |- shift(noCtx, 0) : psi *)
           else (EmptySub, Null)      (* psi |- shift(noCtx, 0) : . *)
         with
         | NoSchema -> (Shift 0, CtxVar psi)
       end
    | DDec (cPsi, TypDecl (name, tA)) ->
       begin match relevant (Whnf.normTyp (tA, Substitution.LF.id)) basis with
       | [] ->
          let (thin_s, cPsi') = inner basis cPsi in
          (* cPsi |- thin_s : cPsi' *)
          (Substitution.LF.comp thin_s (Shift 1), cPsi')
          (* cPsi, x:tA |- thin_s ^ 1 : cPsi' *)
       | nonempty_list ->
          let (thin_s, cPsi') = inner (nonempty_list @ basis) cPsi in
          (* cPsi |- thin_s <= cPsi' *)
          (* cPsi,x:tA |- dot1 thin_s <= cPsi', x:tA'  where tA = [thin_s]([thin_s_inv]tA) *)
          let thin_s_inv = Substitution.LF.invert thin_s in
          (Substitution.LF.dot1 thin_s, DDec (cPsi', TypDecl (name, TClo (tA, thin_s_inv))))
       end
  in
  inner [a] cPsi

let thin' cD a cPsi =
  match Context.ctxVar cPsi with
  | Some (CtxName psi) ->
     begin
       try
         dprintf
           begin fun p ->
           let (_, Decl (_, CTyp _, _)) = Store.FCVar.get psi in
           p.fmt "[thin'] CtxName psi = %a FOUND"
             Id.print psi
           end;
         thin0 cD a cPsi
       with
       | Not_found ->
          dprintf
            begin fun p ->
            p.fmt "[thin'] CtxName psi = %a NOT FOUND"
              Id.print psi
            end;
          (Shift 0, cPsi)
     end
  | _ -> thin0 cD a cPsi


(* BP: Should probably be added

(* thinBlock  (ctx_schema1) (ctx_schema2) =  subst_list

s.t.for each block b_i in ctx_schema1.
     there exists a block b'_k in chtx_schema2.
    s.t.   b_i |- s_i : b'_k
    where s_i is a strengthening substitution.


*)
*)
