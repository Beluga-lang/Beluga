(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   Printing the subordination relation.
   Computing the relation is done in store.ml, as constructors are added.
   
   @author Joshua Dunfield
*)

let dump = ref false

open Syntax.Int.LF
module Types = Store.Cid.Typ

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
 *)

let dump_subord () =
  Printf.printf "## Dumping subordination relation (over %d types)##\n"
                (List.length !Types.entry_list);
  let typeList = List.rev (!Types.entry_list) in
  let dump_entry a b =
    if Types.is_subordinate_to a b then
      print_string (R.render_cid_typ b ^ " ")
    else ()
  in let dump_line a =
      print_string ("--   " ^ R.render_cid_typ a ^ "  |>  ");
      List.iter (dump_entry a) typeList;
      print_string ("\n")
  in
    List.iter (fun a -> dump_line a) typeList
