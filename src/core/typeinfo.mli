val generate_annotations : bool ref
val print_annot : string -> unit
val clear_all : unit -> unit
val type_of_position : int -> int -> string

module Annot : sig
  type entry =
    { typ : string
    }

  val store : (Syntax.Int.Loc.t, entry) Hashtbl.t
  val mk_entry : string -> entry

  val add : Syntax.Int.Loc.t -> entry -> unit
  val get : Syntax.Int.Loc.t -> entry
  val clear : unit -> unit
  val to_string : entry -> string
end

module LF : sig
  type entry =
    { ctx : Syntax.Int.LF.mctx
    ; psi : Syntax.Int.LF.dctx
    ; tc : Syntax.Int.LF.tclo
    }

  val mk_entry : Syntax.Int.LF.mctx -> Syntax.Int.LF.dctx -> Syntax.Int.LF.tclo -> entry

  val add : Syntax.Int.Loc.t -> entry -> string -> unit
  val get : Syntax.Int.Loc.t -> entry
  val clear : unit -> unit
end

module Comp : sig
  type entry =
    { ctx : Syntax.Int.LF.mctx
    ; tc : Syntax.Int.Comp.tclo
    }

  val mk_entry : Syntax.Int.LF.mctx -> Syntax.Int.Comp.tclo -> entry

  val add : Syntax.Int.Loc.t -> entry -> string -> unit
  val get : Syntax.Int.Loc.t -> entry
  val clear : unit -> unit
end

module Sgn : sig
  type typ_or_kind = Typ of Syntax.Int.LF.typ | Kind of Syntax.Int.LF.kind

  type entry =
    { sgn : typ_or_kind
    }

  val mk_entry : typ_or_kind -> entry

  val add : Syntax.Int.Loc.t -> entry -> string -> unit
  val get : Syntax.Int.Loc.t -> entry
  val clear : unit -> unit
end
