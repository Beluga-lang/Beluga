type name     = {
  modules : string list;
  name_hint : string ;
  was_generated : bool ;
  counter : int;
}

let get_module (n : name) : string list = n.modules

let gen_fresh_name (ns : name list) (n : name) : name =
  (* Extract all the numbers from the back *)
  (* let split_name (s : string) : string * int = s, -1 in *)
  (* let s, cnt = split_name n.Id.name_hint in *)
  let cnt' = List.fold_left
    (fun cnt n' -> if n'.name_hint == n.name_hint
      then max n'.counter cnt
      else cnt)
    n.counter ns in
  {n with counter = cnt'+1}
let inc n = {
  modules = n.modules;
  name_hint = n.name_hint;
  was_generated = n.was_generated;
  counter = n.counter + 1;
}


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
      counter = 0} in
  function
    (* If no {!name} is given, create a new unique {!name}.
       This prevents the problem that when a {!Store.Typ.entry} or {!Store.Term.entry} is
       looked up, we never have to compare a {!string option}.
       This prevents the case where two entries appear to refer to the same name
       because {!None} = {!None}. *)
  | MVarName (Some vGen)
  | PVarName (Some vGen)
  | SVarName (Some vGen)
  | BVarName (Some vGen) -> mk_name_helper (vGen())
  | MVarName None
  | SVarName None -> mk_name_helper (Gensym.MVarData.gensym())
  | PVarName None  -> mk_name_helper ("#" ^ Gensym.VarData.gensym())
  | BVarName None
  | NoName     -> mk_name_helper (Gensym.VarData.gensym ())
  | SomeName x  -> x
  | SomeString x -> mk_name_helper x


let string_of_name n =
  let suf = if n.counter == 0 then "" else string_of_int (n.counter) in
   n.name_hint ^ suf

let render_name n =
  let suf = if n.counter == 0 then "" else string_of_int (n.counter) in
  match n.modules with
    | [] -> n.name_hint ^ suf
    | l -> (String.concat "." l) ^ "." ^ (n.name_hint) ^ suf
