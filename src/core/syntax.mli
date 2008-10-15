(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Renaud Germain
   @author Brigitte Pientka
   @author Darin Morrison
*)

(** Syntax for the LF and Computation languages *)



open Id



(** External Syntax *)
module Ext : sig

  module Loc : Camlp4.Sig.Loc

  type kind =
    | Typ    of Loc.t
    | PiKind of Loc.t * typ_decl * kind

  and typ_decl = name * typ

  and typ =
    | Atom  of Loc.t * name * spine
    | PiTyp of Loc.t * typ_decl * typ

  and term =
    | Lam  of Loc.t * name * term
    | Root of Loc.t * head * spine

  and head =
    | Name of Loc.t * name

  and spine =
    | Nil
    | App of term * spine

  type sgn_decl =
    | SgnTyp   of Loc.t * name * kind
    | SgnConst of Loc.t * name * typ

end



(** Internal Syntax *)
module Int : sig

  type kind =
    | Typ
    | PiKind of typ_decl * kind

  and typ_decl = name * typ

  and typ =
    | Atom  of cid_typ * spine
    | PiTyp of typ_decl * typ

  and term =
    | Lam  of name * term
    | Root of head * spine

  and head =
    | BVar  of offset
    | Const of cid_term

  and spine =
    | Nil
    | App of term * spine

  type sgn_decl =
    | SgnTyp   of cid_typ  * kind
    | SgnConst of cid_term * typ

end
