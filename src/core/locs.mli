val gen_loc_info : bool ref
val print_loc_info : string -> unit
val clear_all : unit -> unit

module Locs : sig
	type entry = {	
		expr : string;		
	}

	val mk_entry : string -> entry

	val add : Syntax.Int.Loc.t -> entry -> unit
	val get : Syntax.Int.Loc.t -> entry
	val clear : unit -> unit
end