(* -*- coding: us-ascii; indent-tabs-mode: nil; -*- *)

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
module R = Pretty.Int.NamedRenderer

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
 * Therefore "list-types can contain nat-terms", or equivalently,
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
 *     t : list (suc (suc zero)) -> type.
 *
 * t is type-subordinate to list, and list is type-subordinate to nat, but t is *not*
 * type-subordinate to nat, because the dependent type arguments to t don't
 * include nat-terms.
 *
 * -jd 2010-06
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


(* thin (cO, cD) (tP, cPsi) = (s, cPsi')

   if  cO ; cD |- cPsi ctx
       cO ; cD ; cPsi |- tP <= type
   then
       cO ; cD |- cPsi' ctx 
       cO ; cD; cPsi |- s : cPsi'
*)

let rec separate sep f xs = match xs with
  | [] -> ""
  | [x] -> f x
  | h::t -> f h ^sep ^ separate sep f t

let rec thin (cO, cD) (tP, cPsi) = 
(*      | PiTyp((TypDecl(_x, tA1), _), tA2) -> Types.is_subordinate_to b a *)

  (* The `basis' is the set of type families needed.
     Initially, it is `b' where tP = Atom(_, b, _). *)
  let rec inner (basis : Id.cid_typ list) cPsi =
    let basisToString basis = separate ", " (fun type_in_basis -> R.render_cid_typ type_in_basis) basis in
    let rec relevant = function
        | Atom(_, a, _spine) ->
            Types.freeze a;
            if List.exists (fun type_in_basis -> Types.is_subordinate_to type_in_basis a) basis then
              (* there is some `b' in basis such that `a'-terms can appear in `b'-terms, that is,
                 `a'-terms can appear in something we need *)
              [a]
            else
              (
                dprint (fun () -> "Denying that " ^ R.render_cid_typ a ^ 
                          " can appear in any of the following: " ^ basisToString basis);
              [])
        | PiTyp((TypDecl(_x, tA1), _), tA2) ->
            norm_relevant tA1 @ norm_relevant tA2
        | Sigma typRec -> norm_relevantTypRec typRec

    and relevantTypRec = function
      | SigmaLast tA -> relevant tA
      | SigmaElem (_name, tA, typRec) ->
          norm_relevant tA @ norm_relevantTypRec typRec

    and relevantSchema (Schema sch_elems) =
      List.exists (function SchElem(_some_part, typRec) -> not (null (relevantTypRec typRec))) sch_elems

    and norm_relevant tA = normify relevant Whnf.normTyp tA
    and norm_relevantTypRec typRec = normify relevantTypRec Whnf.normTypRec typRec 

    in
      match cPsi with
        | Null -> (Shift(NoCtxShift, 0),  Null) (* . |- shift(noCtx, 0) : . *)

        | CtxVar psi -> 
            if relevantSchema (Schema.get_schema (Context.lookupCtxVarSchema cO psi)) then
              ( (*print_string "Keeping context variable\n"; *)
                (Shift(NoCtxShift, 0),  CtxVar psi))  (* psi |- shift(noCtx, 0) : psi *)
            else
              ( (* print_string ("Denying that the context variable is relevant to anything in " ^ basisToString basis ^ "\n"); *)
               (Shift(CtxShift psi, 0),  Null) )  (* psi |- shift(noCtx, 0) : . *)

        | DDec(cPsi, TypDecl(name, tA)) ->
            begin match relevant tA with
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
