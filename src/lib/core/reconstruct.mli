(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
*)

open Syntax
open Id
open Error

exception Error of Syntax.Loc.t option * error
exception Violation of string

val recSgnDecl : Ext.Sgn.decl -> Int.Sgn.decl
