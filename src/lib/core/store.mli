(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



open Id
open Syntax.Int



module Cid : sig

  module Typ : sig

    type entry          = private {
      name : name
    ; kind : kind
    }

    val mk_entry        : name -> kind -> entry


    type t

    val add             : entry -> cid_typ

    val get             : cid_typ -> entry

    val index_of_name   : name -> cid_typ

    val clear           : unit -> unit

  end



  module Term : sig

    type entry          = private {
      name : name
    ; typ  : typ
    }

    val mk_entry        : name -> typ -> entry


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
