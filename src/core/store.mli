(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(**
   @author Darin Morrison
*)



module Cid : sig

  open Syntax.Int



  module Typ : sig

    type entry          = private {
      name : Id.name
    ; kind : LF.kind
    }

    val mk_entry             : Id.name -> LF.kind -> entry

    val string_of_entry      : entry -> string


    type t

    val add           : entry -> Id.cid_typ

    val get           : Id.cid_typ -> entry

    val index_of_name : Id.name -> Id.cid_typ

  end



  module Term : sig

    type entry          = private {
      name : Id.name
    ; typ  : LF.typ
    }

    val mk_entry        : Id.name -> LF.typ -> entry

    val string_of_entry : entry -> string


    type t

    val add             : entry -> Id.cid_term

    val get             : Id.cid_term -> entry

    val index_of_name   : Id.name -> Id.cid_term

  end



end



module DataVar : sig

  type entry          = private {
    name : Id.name
  }

  val mk_entry        : Id.name -> entry

  val string_of_entry : entry -> string


  type t

  val create          : unit -> t

  val extend          : t -> entry -> t

  val get             : t -> Id.var  -> entry

  val index_of_name   : t -> Id.name -> Id.offset

end
