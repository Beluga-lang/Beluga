(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

open Id

open Syntax.Int

module Cid : sig

  module Typ : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      kind               : LF.kind
    }

    val mk_entry      : name -> LF.kind -> int -> entry
    type t
    val add           : entry -> cid_typ
    val get           : cid_typ -> entry
    val index_of_name : name -> cid_typ
    val clear         : unit -> unit

  end


  module Term : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : LF.typ
    }

    val mk_entry      : name -> LF.typ -> int -> entry
    type t
    val add           : entry -> cid_term
    val get           : cid_term -> entry
    val index_of_name : name -> cid_term
    val clear         : unit -> unit

  end


  module Comp : sig

    type entry = private {
      name               : name;
      implicit_arguments : int;
      typ                : Comp.typ;
      prog               : Comp.exp_chk
    }

    val mk_entry      : name -> Comp.typ -> int -> Comp.exp_chk -> entry
    type t
    val add           : entry -> cid_prog
    val get           : cid_prog -> entry
    val index_of_name : name -> cid_prog
    val clear         : unit -> unit

  end


  module Schema : sig

    type entry = private {
      name   : name;
      schema : LF.schema
    }

    val mk_entry        : name -> LF.schema -> entry
    type t
    val add             : entry -> cid_schema
    val get             : cid_schema -> entry
    val get_schema      : cid_schema -> LF.schema
    val index_of_name   : name -> cid_schema
    val clear           : unit -> unit

  end

end

val clear : unit -> unit


module BVar : sig

  type entry = private {
    name : name
  }

  val mk_entry      : name -> entry
  type t
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val length        : t -> int
  val index_of_name : t -> name -> offset

end


module FVar : sig

  val add   : name -> LF.typ -> unit
  val get   : name -> LF.typ
  val clear : unit -> unit

end


module FMVar : sig

  val add   : name -> (LF.typ * LF.dctx) -> unit
  val get   : name -> (LF.typ * LF.dctx)
  val clear : unit -> unit

end


module FPVar : sig

  val add   : name -> (LF.typ * LF.dctx) -> unit
  val get   : name -> (LF.typ * LF.dctx)
  val clear : unit -> unit

end


module Var : sig

  type entry = private {
    name : name
  }

  val mk_entry      : name -> entry
  type t
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val index_of_name : t -> name -> offset

end


module CVar : sig

  type entry = private {
    name : name
  }

  val mk_entry      : name -> entry
  type t
  val create        : unit -> t
  val extend        : t -> entry -> t
  val get           : t -> var  -> entry
  val index_of_name : t -> name -> offset
  val append        : t -> t -> t
  val length        : t -> int

end

