open Support
open Beluga_syntax

val generate_annotations : bool ref
val print_annot : string -> unit
val clear_all : unit -> unit
val type_of_position : int -> int -> string

module Annot : sig
  type entry =
    { typ : string
    }

  val store : (Location.t, entry) Hashtbl.t
  val mk_entry : string -> entry

  val add : Location.t -> entry -> unit
  val get : Location.t -> entry
  val clear : unit -> unit
  val to_string : entry -> string
end

module LF : sig
  open Synint.LF

  type entry =
    { ctx : mctx
    ; psi : dctx
    ; tc : tclo
    }

  val mk_entry : mctx -> dctx -> tclo -> entry

  val add : Location.t -> entry -> string -> unit
  val get : Location.t -> entry
  val clear : unit -> unit
end

module Comp : sig
  open Synint.LF
  open Synint.Comp
  type entry =
    { ctx : mctx
    ; tc : tclo
    }

  val mk_entry : mctx -> tclo -> entry

  val add : Location.t -> entry -> string -> unit
  val get : Location.t -> entry
  val clear : unit -> unit
end

module Sgn : sig
  open Synint.LF
  type typ_or_kind = Typ of typ | Kind of kind

  type entry =
    { sgn : typ_or_kind
    }

  val mk_entry : typ_or_kind -> entry

  val add : Location.t -> entry -> string -> unit
  val get : Location.t -> entry
  val clear : unit -> unit
end
