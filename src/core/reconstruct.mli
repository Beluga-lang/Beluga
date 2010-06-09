(**
   @author Renaud Germain
*)

open Syntax
open Id
open Error

exception Error of Syntax.Loc.t option * error
exception Violation of string

(* val recSgnDecl : Ext.Sgn.decl -> Int.Sgn.decl
  val recSgnDecls : Ext.Sgn.decl list -> Int.Sgn.decl list
*)

val recSgnDecl : Ext.Sgn.decl -> unit

val recSgnDecls : Ext.Sgn.decl list -> unit
