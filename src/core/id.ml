type name     = {
  modules : string list;
  hint_name : string ;
  hint_cnt : int option;
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
  let s, cnt = split_name n.hint_name in
  {n with hint_name = s;
          hint_cnt =
            match n.hint_cnt with
            | None -> cnt
            | Some old_cnt  ->
               match cnt with
               | None -> n.hint_cnt
               | Some name_cnt ->
                  Some (int_of_string ((string_of_int name_cnt) ^ (string_of_int old_cnt)))}


let gen_fresh_name (ns : name list) (n : name) : name =
  let inc_iopt : int option -> int option = function
    | None -> Some 0
    | Some j -> Some (j+1) in
  let rec next_unused y xs =
    if List.mem y xs
    then next_unused (inc_iopt y) xs
    else y in
  let cnts = List.fold_left
     (fun acc n' -> if n'.hint_name = n.hint_name
                    then n'.hint_cnt::acc else acc) [] ns in
  {n with hint_cnt = next_unused n.hint_cnt cnts}

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
    let nm', cnt = split_name nm in
    { modules = modules;
      hint_name = nm';
      was_generated = true;
      counter = 0;
      hint_cnt = cnt } in
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
  | SomeName x  -> sanitize_name x
  | SomeString x -> mk_name_helper x


let string_of_name (n : name) : string =
  let suf = match n.hint_cnt with
      | None -> ""
      | Some cnt -> (string_of_int cnt) in
  n.hint_name ^ suf 

let render_name n = match n.modules with
    | [] -> string_of_name n
    | l  -> (String.concat "." l) ^ "." ^ (string_of_name n) 

(*******************************************************************************************************)
let string_of_name_latex (n : name) : string =
  let suf = match n.hint_cnt with
      | None -> ""
      (* cnt as subscript, better readability in LaTex *)
      | Some cnt -> "_" ^ (string_of_int cnt) 
  in 
  let name = Str.global_replace (Str.regexp "_\\|-\\|\\^") "" n.hint_name in
  let name = Str.global_replace (Str.regexp "&") "and" name in
  name ^ suf

let render_name_latex n = match n.modules with
    | [] -> string_of_name_latex n
    | l  -> (String.concat "." l) ^ "." ^ (string_of_name_latex n) 



