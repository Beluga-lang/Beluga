val generate_annotations : bool ref
val print_annot : string -> unit
val clear_all : unit -> unit

module Annot : sig
	type entry = {
		typ : string	
	}

	val mk_entry : string -> entry

	val add : Syntax.Int.Loc.t -> entry -> unit
	val get : Syntax.Int.Loc.t -> entry
	val clear : unit -> unit
	val to_string : entry -> string
	
end

module LF : sig
	type entry = {
		ctx : Syntax.Int.LF.mctx;
		psi : Syntax.Int.LF.dctx;
		tc : Syntax.Int.LF.tclo
	}

	val mk_entry : Syntax.Int.LF.mctx -> Syntax.Int.LF.dctx -> Syntax.Int.LF.tclo -> entry

	val add : Syntax.Int.Loc.t -> entry -> string -> unit
	val get : Syntax.Int.Loc.t -> entry
	val clear : unit -> unit
	
end

module Comp : sig
	type entry = {
		ctx : Syntax.Int.LF.mctx;
		tc : Syntax.Int.Comp.tclo
	}

	val mk_entry : Syntax.Int.LF.mctx -> Syntax.Int.Comp.tclo -> entry

	val add : Syntax.Int.Loc.t -> entry -> string -> unit
	val get : Syntax.Int.Loc.t -> entry
	val clear : unit -> unit
	
end