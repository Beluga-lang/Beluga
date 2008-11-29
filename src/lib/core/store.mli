(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Id
open Syntax.Int.LF



module Cid : sig

  module Typ : sig

    type entry          = private {
      name                 : name
      ; implicit_arguments : int
      ; kind               : kind
    }

    val mk_entry        : name -> kind -> int -> entry


    type t

    val add             : entry -> cid_typ

    val get             : cid_typ -> entry

    val index_of_name   : name -> cid_typ

    val clear           : unit -> unit

  end



  module Term : sig

    type entry          = private {
      name                 : name
      ; implicit_arguments : int
      ; typ                : typ
    }

    val mk_entry        : name -> typ -> int -> entry


    type t

    val add             : entry -> cid_term

    val get             : cid_term -> entry

    val index_of_name   : name -> cid_term

    val clear           : unit -> unit

  end

end

val clear : unit -> unit



module BVar : sig

  type entry          = private {
    name : name
  }

  val mk_entry        : name -> entry


  type t

  val create          : unit -> t

  val extend          : t -> entry -> t

  val get             : t -> var  -> entry

  val index_of_name   : t -> name -> offset

end


module FVar : sig

  val add             : name -> typ -> unit
  val get             : name -> typ
  val clear           : unit -> unit

end
