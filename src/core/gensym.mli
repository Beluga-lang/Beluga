(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



(** Functionality for generating unique symbols *)
module type GENSYM = sig

  (** Generate a unique symbol.  Generated symbols are guaranteed
      unique because they always end in [%], making them unparsable
      and thus impossible to use directly in any program. *)
  val gensym : unit -> string

end


(** Symbol generation for data variables.  Symbols take the form
    [a,..., z, a1, ...z1, a2, ...] *)
module VarData : GENSYM
