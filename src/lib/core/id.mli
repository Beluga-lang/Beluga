(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



(** A `name' represents the original named representation of a
    variable.  These are used primarily during parsing and pretty
    printing.  Names should never be constructed directly.  See
    `mk_name'. *)
type name     = private {
  string_of_name : string
}

(** A constant identifier for types *)
type cid_typ  = int

(** A constant identifier for terms *)
type cid_term = int

(** An offset to be used during shifting for a DeBruijn variable
    representation *)
type offset   = int

(** The DeBruijn representation of a variable *)
type var      = int


(** Smart constructor for `name'.  If `None' or `Some ""' are given,
    `mk_name' generates a `name' with a guaranteed unique `string'. *)
val mk_name : string option -> name
