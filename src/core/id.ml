open Support

let (dprintf, _, _) = Debug.(makeFunctions' (toFlags [11]))
open Debug.Fmt

type name     = {
  modules : string list;
  hint_name : string ;
  hint_cnt : int option;
  was_generated : bool ;
  counter : int;
  loc : Location.t
}

let loc_of_name n = n.loc

(** Computes a string representation of a name, without modules. *)
let string_of_name (n : name) : string =
  let suf =
    match n.hint_cnt with
    | None -> ""
    | Some cnt -> (string_of_int cnt)
  in
  n.hint_name ^ suf

(** Computes a string representation of a name, with all modules. *)
let render_name n =
  match n.modules with
  | [] -> string_of_name n
  | l  -> (String.concat "::" l) ^ "::" ^ (string_of_name n)

(** Does the same as `render_name', but for use with pretty-printing. *)
let print ppf n =
  let open Format in
  fprintf ppf "%a%s"
    (pp_print_list ~pp_sep: (fun _ _ -> ())
       (fun ppf x -> fprintf ppf "%s::" x))
    n.modules
    (string_of_name n)

(** Displays a list of space separated names. *)
let print_list ppf ns =
  let open Format in
  pp_print_list ~pp_sep: pp_print_space print ppf ns

(* For reporting whether a name is used in a context. *)
type max_usage =
  [ `used of int option
  | `unused
  ]

(** Extract the base name of a variable. *)
let base_name (x : name) : string = x.hint_name

let modify_number f name =
  { name with hint_cnt = f name.hint_cnt }

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

let inc_hint_cnt : int option -> int option = function
  | None -> Some 1
  | Some k -> Some (k + 1)

let gen_fresh_name (ns : name list) (n : name) : name =
  let rec next_unused y xs =
    if List.mem y xs
    then next_unused (inc_hint_cnt y) xs
    else y in
  let cnts =
    let open Maybe in
    filter_map
      begin fun n' ->
      Misc.String.equals n'.hint_name n.hint_name
      |> of_bool
      $> Misc.const n'.hint_cnt
      end
      ns
  in
  {n with hint_cnt = next_unused n.hint_cnt cnts}

let max_usage (ctx : name list) (s : string) : max_usage =
  let same_head s name =
    Misc.String.equals name.hint_name s
  in
  let max' k name = max k name.hint_cnt in
  match Nonempty.of_list (List.filter (same_head s) ctx) with
  | None ->
     dprintf
       begin fun p ->
       p.fmt "[max_usage] @[<v 2>%s is unused in@,\
              @[%a@]@]"
         s
         print_list
         ctx
       end;
     `unused
  | Some names ->
     let k = Nonempty.fold_left (fun x -> x.hint_cnt) max' names in
     dprintf
       begin fun p ->
       p.fmt "[max_usage] @[<v 2>%s is USED, k = %a in@,\
              @[%a@]@]"
         s
         (Maybe.show Format.pp_print_int) k
         print_list ctx
       end;
     `used k

type module_id = int

type cid_typ    = module_id * int
type cid_term   = module_id * int
type cid_schema = module_id * int
type cid_coercion = module_id * int
type cid_comp_typ = module_id * int
type cid_comp_cotyp = module_id * int
type cid_comp_const = module_id * int
type cid_comp_dest = module_id * int
type cid_comp_typdef = module_id * int
type cid_prog   = module_id * int

(** Used to identify a group of mutually proven theorems. *)
type cid_mutual_group = int

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

let mk_name ?(loc = Location.ghost) ?(modules=[]) : name_guide -> name =
  let mk_name_helper (nm: string) : name =
    let nm', cnt = split_name nm in
    { modules = modules;
      hint_name = nm';
      was_generated = true;
      counter = 0;
      hint_cnt = cnt;
      loc
    } in
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

let equals n1 n2 =
  Misc.String.equals (string_of_name n1) (string_of_name n2)

let cid_equals (l1, n1) (l2, n2) =
  l1 = l2 && n1 = n2

let mk_blank = function
  | Some loc -> mk_name ~loc: loc (SomeString "_")
  | None -> mk_name (SomeString "_")
