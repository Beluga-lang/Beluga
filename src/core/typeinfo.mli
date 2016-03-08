val generate_annotations : bool ref
val print_annot : string -> unit
val clear_all : unit -> unit
val type_of_position : int -> int -> Syntax.Loc.t option * string

module Annot : sig
	type entry = {
		typ : string
	}
	val store : (Syntax.Int.Loc.t, entry) Hashtbl.t
	val mk_entry : string -> entry

	val add : Syntax.Int.Loc.t -> string -> unit
	val get : Syntax.Int.Loc.t -> entry
	val clear : unit -> unit
	val to_string : entry -> string

end

module Comp : sig
  val annotate_comp_exp_chk : Syntax.Ext.Comp.exp_chk -> Annotated.Comp.exp_chk -> unit
end

module Sgn : sig
  val annotate_sgn_typ : Syntax.Int.Loc.t -> Syntax.Int.LF.kind -> unit
  val annotate_sgn_const : Syntax.Int.Loc.t -> Syntax.Int.LF.typ -> unit

end
