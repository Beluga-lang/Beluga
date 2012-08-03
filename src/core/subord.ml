(**
   Printing the subordination relation.
   Computing the relation is done in store.ml, as constructors are added.
   Also has `thin', which uses subordination to generate a substitution that
    doesn't use irrelevant parts of a context.

   @author Joshua Dunfield
*)

let dump = ref false

open Syntax.Int.LF
module Types = Store.Cid.Typ
module Schema = Store.Cid.Schema

module P = Pretty.Int.DefaultPrinter
module R = Store.Cid.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [28])

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

let dump_subord () =
  Printf.printf "## Dumping subordination relation (over %d types) ##\n"
                (List.length !Types.entry_list);
  let typeList = List.rev (!Types.entry_list) in
  let dump_entry a b =
    if Types.is_subordinate_to a b then print_string (R.render_cid_typ b ^ " ")

  in let dump_line a =
      print_string ("--   " ^ R.render_cid_typ a ^ "  |>  ");
      List.iter (dump_entry a) typeList;
      print_string ("\n")
  in
    List.iter (fun a -> dump_line a) typeList

let dump_typesubord () =
  Printf.printf "## Dumping type-level subordination relation (over %d types) ##\n"
                (List.length !Types.entry_list);
  let typeList = List.rev (!Types.entry_list) in
  let dump_entry a b =
    if Types.is_typesubordinate_to a b then print_string (R.render_cid_typ b ^ " ")

  in let dump_line a =
      print_string ("--[type]   " ^ R.render_cid_typ a ^ "  |>  ");
      List.iter (dump_entry a) typeList;
      print_string ("\n")
  in
    List.iter (fun a -> dump_line a) typeList



let null = function [] -> true
                   | _ -> false

(* Apply the `normer' function with the identity substitution,
   then call `f' on the result *)
let normify f normer =
  fun thing -> f (normer (thing, Substitution.LF.id))

let rec separate sep f xs = match xs with
  | [] -> ""
  | [x] -> f x
  | h::t -> f h ^sep ^ separate sep f t

let basisToString basis =
  separate ", " (fun type_in_basis -> R.render_cid_typ type_in_basis) basis


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
let rec relevant tA basis = (match tA with
  | Atom(_, a, _spine) ->
      Types.freeze a;
      if List.exists (fun type_in_basis -> Types.is_subordinate_to type_in_basis a
                        || a = type_in_basis) basis then
        (* there is some `b' in basis such that `a'-terms can appear in `b'-terms, that is,
           `a'-terms can appear in something we need *)
        [a]
      else
        (
          dprint (fun () -> "Denying that " ^ R.render_cid_typ a ^
                    " can appear in any of the following: " ^ basisToString basis);
(*          dump_subord () ;
          dump_typesubord () ; *)
          [])
  | PiTyp((TypDecl(_x, tA1), _), tA2) ->
      (relevant tA1 basis) @ (relevant tA2 basis)
  | Sigma typRec -> relevantTypRec typRec basis
                            )

and relevantTypRec tRec basis = (match tRec with
  | SigmaLast tA -> relevant tA basis
  | SigmaElem (_name, tA, typRec) ->
      (relevant tA  basis)@ (relevantTypRec typRec basis))

and relevantSchema (Schema sch_elems) basis =
  List.exists (function SchElem(_some_part, typRec) ->
                 not (null (relevantTypRec typRec basis))) sch_elems

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

let rec thin (cO, cD) (tP, cPsi) =
  (*inner basis cPsi = (s, cPsi')

     if basis is a list of type families
        cO ; cD |- cPsi ctx
     then
        cPsi' only contains those declarations whose types is
        relevant to constructing elements of type families
        in basis.

     Initially, basis is `b' where tP = Atom(_, b, _).
  *)
  let rec inner (basis : Id.cid_typ list) cPsi = match cPsi with
    | Null -> (Shift(NoCtxShift, 0),  Null) (* . |- shift(noCtx, 0) : . *)
    | CtxVar psi ->
        let schema = begin match psi with
          | CtxOffset _ -> Context.lookupCtxVarSchema cD psi
          | CInst ( _, _ , cid_schema, _, _ ) -> cid_schema
        end
        in
        if relevantSchema (Schema.get_schema schema) basis then
          ( (*print_string "Keeping context variable\n"; *)
            (Shift(NoCtxShift, 0),  CtxVar psi))  (* psi |- shift(noCtx, 0) : psi *)
        else
          ( (* print_string ("Denying that the context variable is relevant to anything in " ^ basisToString basis ^ "\n"); *)
            (Shift(CtxShift psi, 0),  Null) )  (* psi |- shift(noCtx, 0) : . *)
    | DDec(cPsi, TypDecl(name, tA)) ->
        begin match relevant (Whnf.normTyp (tA, Substitution.LF.id)) basis with
          | [] ->
            let (thin_s, cPsi') = inner  basis cPsi in
              (* cPsi |- thin_s : cPsi' *)
              (Substitution.LF.comp thin_s (Shift (NoCtxShift, 1)),  cPsi')
              (* cPsi, x:tA |- thin_s ^ 1 : cPsi' *)
          | nonempty_list ->
            let (thin_s, cPsi') = inner (nonempty_list @ basis) cPsi in
              (* cPsi |- thin_s <= cPsi' *)
              (* cPsi,x:tA |- dot1 thin_s <= cPsi', x:tA'  where tA = [thin_s]([thin_s_inv]tA) *)
            let thin_s_inv      = Substitution.LF.invert thin_s in
              (Substitution.LF.dot1 thin_s,  DDec(cPsi', TypDecl(name, TClo(tA, thin_s_inv))))
        end
  in
    inner (match tP with Atom(_, a, _spine) -> [a]) cPsi





let rec thin' cD a cPsi =
  (*inner basis cPsi = (s, cPsi')

     if basis is a list of type families
        cO ; cD |- cPsi ctx
     then
        cPsi' only contains those declarations whose types is
        relevant to constructing elements of type families
        in basis.

     Initially, basis is `b' where tP = Atom(_, b, _).
  *)
  let rec inner (basis : Id.cid_typ list) cPsi = match cPsi with
    | Null -> (Shift(NoCtxShift, 0),  Null) (* . |- shift(noCtx, 0) : . *)

    | CtxVar (psi) ->
        let schema = begin match psi with
          | CtxOffset _ -> Context.lookupCtxVarSchema cD psi
          | CInst ( _, _ , cid_schema, _, _ ) -> cid_schema
        end
        in
        if relevantSchema (Schema.get_schema schema) basis then
          ( (*print_string "Keeping context variable\n"; *)
            (Shift(NoCtxShift, 0),  CtxVar psi))  (* psi |- shift(noCtx, 0) : psi *)
        else
          ( (* print_string ("Denying that the context variable is relevant to anything in " ^ basisToString basis ^ "\n"); *)
            (Shift(CtxShift psi, 0),  Null) )  (* psi |- shift(noCtx, 0) : . *)
    | DDec(cPsi, TypDecl(name, tA)) ->
        begin match relevant (Whnf.normTyp (tA, Substitution.LF.id)) basis with
          | [] ->
            let (thin_s, cPsi') = inner  basis cPsi in
              (* cPsi |- thin_s : cPsi' *)
              (Substitution.LF.comp thin_s (Shift (NoCtxShift, 1)),  cPsi')
              (* cPsi, x:tA |- thin_s ^ 1 : cPsi' *)
          | nonempty_list ->
            let (thin_s, cPsi') = inner (nonempty_list @ basis) cPsi in
              (* cPsi |- thin_s <= cPsi' *)
              (* cPsi,x:tA |- dot1 thin_s <= cPsi', x:tA'  where tA = [thin_s]([thin_s_inv]tA) *)
            let thin_s_inv      = Substitution.LF.invert thin_s in
              (Substitution.LF.dot1 thin_s,  DDec(cPsi', TypDecl(name, TClo(tA, thin_s_inv))))
        end
  in
    inner [a] cPsi
