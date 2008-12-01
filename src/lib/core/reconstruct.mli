(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Darin Morrison
*)

open Syntax
open Id

(** Approximate Simple Syntax *)
module Apx : sig

  module LF : sig

    type kind =                     (* kinds                          *)
      | Typ                         (* K ::= type                     *)
      | PiKind of typ_decl * kind   (*   | Pi x:A.K                   *)

    and typ_decl =
      | TypDecl of name * typ

    and typ =                       (* types                          *)
      | Atom  of cid_typ * spine    (* A ::= a M1 ... Mn              *)
      | PiTyp of typ_decl * typ     (*   | Pi x:A.B                   *)

    and normal =                    (* normal terms                   *)
      | Lam  of name * normal       (* M ::= \x.M                     *)
      | Root of head * spine        (*   | h . S                      *)

    and head =
      | BVar  of offset             (* H ::= x                        *)
      | Const of cid_term           (*   | c                          *)
      | FVar  of name               (*   | X                          *)

    and spine =                     (* spine                          *)
      | Nil                         (* S ::= Nil                      *)
      | App of normal * spine       (*   | M . S                      *)

  end

end

val reconstruct_sgn_decl : Ext.LF.sgn_decl -> Int.LF.sgn_decl
