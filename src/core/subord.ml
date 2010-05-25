(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   Deciding the subordination relation
   
   @author Joshua Dunfield
*)

open Syntax.Int.LF
module Types = Store.Cid.Typ
module Constructors = Store.Cid.Term

module P = Pretty.Int.DefaultPrinter
module R = Pretty.Int.NamedRenderer

let (dprint, dprnt) = Debug.makeFunctions (Debug.toFlags [28])

(* getConstructorsAndTypes : Id.cid_typ -> (Id.cid_term * typ) list
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

let getTypes a =
  List.map Types.get (!Types.entry_list)


(*
 * DEFINITIONS
 *
 * The type B is subordinate to the type A if a term of type A can appear in a term of type B.
 * Subordination is entirely a data-level (LF) notion; it can be determined from the
 * LF signature alone.
 *
 * The usual reference for subordination is Roberto Virga's 1999 thesis.  However, Virga
 *  does not call it subordination; rather, he uses a "dependence relation" (pp. 55-59),
 *  also called "containment".
 *)

(* b subordinates a === a is subordinate to b === terms of type `a' can appear in terms of type `b' *)
let rec appears trail a b =
  if List.exists ((=) (a, b)) trail then
    false
  else
    let trail = (a, b)::trail in
    let (*tA_constructors = getConstructorsAndTypes a
    and*) b_constructors = getConstructorsAndTypes b in
      List.exists
        (fun (b_constructor, tB) -> appears_typ_top trail a tB)
        b_constructors

and appears_typ_top trail a = function
  | Atom(_, _b, _spine) ->
      false
  | PiTyp((TypDecl(name, tA1), _depend), tA2) ->
      appears_typ trail a tA1
      ||
      appears_typ trail a tA2
(*  | Sigma _ -> *)

and appears_typ trail a = function
  | Atom(_, b, _spine) ->
      a = b || appears trail a b
  | PiTyp((TypDecl(name, tA1), _depend), tA2) ->
      appears_typ trail a tA1
      ||
      appears_typ trail a tA2


let dump_subord () =
  print_string ("## Dumping subordination relation ##\n");
  let typeList = !Types.entry_list in
  let dump_entry a b =
    let indication = if appears [] a b then "  |>  " else "  /_  " in
      print_string ("--    " ^ R.render_cid_typ a ^ indication ^ R.render_cid_typ b ^ "\n")
  in
    List.iter (fun a -> List.iter (fun b -> dump_entry a b) typeList) typeList
