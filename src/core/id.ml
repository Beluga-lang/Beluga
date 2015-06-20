type name     = {
  modules : string list;
  name_hint : string ;
  was_generated : bool ;
  counter : int;
}

let get_module (n : name) : string list = n.modules

let inc (n : name) : name  =
  {n with counter = n.counter + 1}

let split_name (s : string) : string * int option =
  try
    let pos = Str.search_backward (Str.regexp "[^0-9]") s (String.length s) + 1 in
    Str.string_before s pos, Some (int_of_string (Str.string_after s pos))
  with
  | Failure _ -> s, None
  | Not_found -> raise (Failure "Cannot split an empty name")

let sanitize_name (n : name) : name =
  let s, cnt = split_name n.name_hint in
  if (n.counter = 0)
  then {n with name_hint = s;
               counter = match cnt with
                         | None -> 0
                         | Some cnt' -> cnt'}
  else {n with name_hint = s;
               counter = match cnt with
                         | None -> n.counter
                         | Some cnt' ->
                            int_of_string ((string_of_int cnt') ^ (string_of_int n.counter))}

(* Very inefficient, but works, unlike splitting names within mk_name *)
let gen_fresh_name (ns : name list) (n : name) : name =
  let ns = List.map sanitize_name ns in
  let n = sanitize_name n in
  let rec next_unused y xs =
    if List.mem y xs
    then next_unused (y+1) xs
    else y in
  let cnts = List.fold_left
     (fun acc n' -> if n'.name_hint == n.name_hint
                    then n'.counter::acc else acc) [] ns in
  {n with counter = next_unused n.counter cnts}
  (* This variant is faster, but generates higher indices *)
  (* let cnt' = List.fold_left *)
  (*   (fun cnt n' -> if n'.name_hint == n.name_hint *)
  (*     then max n'.counter cnt *)
  (*     else cnt) *)
  (*   n.counter ns in *)
  (* {n with counter = cnt' + 1} *)

type module_id = int

type cid_typ    = module_id * int

type cid_term   = module_id * int

type cid_schema = module_id * int

type cid_coercion = module_id * int

type cid_comp_typ = module_id * int

type cid_comp_cotyp = module_id * int

type cid_comp_const = module_id * int

type cid_comp_dest = module_id * int

type cid_prog   = module_id * int

type offset     = int

type var        = int

type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | SVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of name
  | SomeString of string

let mk_name ?(modules=[]) : name_guide -> name =
  let mk_name_helper (nm: string) : name =
    { modules = modules;
      name_hint = nm;
      was_generated = true;
      counter = 0 } in
  function
    (* If no {!name} is given, create a new unique {!name}.
       This prevents the problem that when a {!Store.Typ.entry} or {!Store.Term.entry} is
       looked up, we never have to compare a {!string option}.
       This prevents the case where two entries appear to refer to the same name
       because {!None} = {!None}. *)
  | MVarName (Some vGen)
  | SVarName (Some vGen)
  | PVarName (Some vGen)
  | BVarName (Some vGen) -> mk_name_helper (vGen())
  | MVarName None
  | SVarName None -> mk_name_helper (Gensym.MVarData.gensym())
  | PVarName None -> mk_name_helper ("#" ^ Gensym.VarData.gensym())
  | BVarName None
  | NoName     -> mk_name_helper (Gensym.VarData.gensym ())
  | SomeName x  -> x
  | SomeString x -> mk_name_helper x


let string_of_name (n : name) : string =
  let suf = if n.counter == 0 then "" else (string_of_int n.counter) in
  n.name_hint ^ suf

let render_name n = match n.modules with
    | [] -> string_of_name n
    | l  -> (String.concat "." l) ^ "." ^ (string_of_name n)
