(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(** Functionality for generating unique symbols *)
module type GENSYM = sig

  (** Generate a unique symbol.  Generated symbols are guaranteed
      unique because they always end in [%], making them unparsable
      and thus impossible to use directly in any program. *)
  val gensym : unit -> string
  val name_gensym : string -> (unit -> string)

  val reset : unit -> unit
end


(** Symbol generation for data variables.  Symbols take the form
    [a,..., z, a1, ...z1, a2, ...] *)
module VarData : GENSYM

module MVarData : GENSYM

val reset : unit -> unit

