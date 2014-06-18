module Loc = Syntax.Int.Loc

let gen_loc_info = ref false;

module Locs = struct
	type entry = {
		expr : string
	}

	let mk_entry (e : string) : entry =
	{
		expr = e
	}

	let store 	 = Hashtbl.create 0
	let add 	 = Hashtbl.add store
	let get 	 = Hashtbl.find store
	let clear () = Hashtbl.clear store

	let rec print_loc (pp : out_channel) (name : string) : unit =
	begin
		let sorted =
			let l = Hashtbl.fold (fun k v acc -> (k, v)::acc) store [] in
				List.sort (fun (key1, _) (key2, _) -> compare key1 key2) l in
					let f = print_one pp name in
					ignore (List.iter f sorted);
					close_out pp
	end

	and print_one (pp : out_channel) (name : string) (tup : Loc.t * entry) : unit =
		begin
			let (loc, entry) = tup in
				let e = entry.expr in
					output_string pp e;
					output_string pp "\n\tat: ";
					output_string pp (Syntax.Loc.to_string loc);
					output_string pp "\n\tposition: ";
					output_string pp ((string_of_int (Syntax.Loc.start_off loc)) ^ ", " ^ (string_of_int (Syntax.Loc.stop_off loc)));
					output_string pp "\n\n"
		end

end

let clear_all () : unit =
	Locs.clear ()

let print_loc_info (name : string) : unit =
	let pp = open_out ((fun n -> String.sub n 0 (String.rindex n '.')) name ^ ".locs") in
	Locs.print_loc pp name