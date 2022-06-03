open Support

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [ 11 ]))

open Debug.Fmt

type t =
  { modules : string list
  ; hint_name : string
  ; hint_cnt : int option
  ; location : Location.t
  }

(* For reporting whether a name is used in a context. *)
type max_usage =
  [ `used of int option
  | `unused
  ]

let[@inline] location { location; _ } = location

(** Computes a string representation of a name, without modules. *)
let string_of_name n =
  let suf =
    match n.hint_cnt with
    | None -> ""
    | Some cnt -> string_of_int cnt
  in
  n.hint_name ^ suf

(** Computes a string representation of a name, with all modules. *)
let render_name n =
  match n.modules with
  | [] -> string_of_name n
  | l -> String.concat "::" l ^ "::" ^ string_of_name n

let pp ppf n =
  Format.fprintf ppf "%a%s"
    (Format.pp_print_list
       ~pp_sep:(fun _ _ -> ())
       (fun ppf x -> Format.fprintf ppf "%s::" x))
    n.modules (string_of_name n)

let show n =
  match n.modules with
  | [] -> string_of_name n
  | l -> String.concat "::" l ^ "::" ^ string_of_name n

let pp_list = List.pp ~pp_sep:Format.pp_print_space pp

(** Extract the base name of a variable. *)
let base_name x = x.hint_name

let modify_number f name = { name with hint_cnt = f name.hint_cnt }

let get_module n = n.modules

let split_name s =
  try
    let pos =
      Str.search_backward (Str.regexp "[^0-9]") s (String.length s) + 1
    in
    (Str.string_before s pos, Some (int_of_string (Str.string_after s pos)))
  with
  | Failure _ -> (s, None)
  | Not_found -> raise (Failure "Cannot split an empty name")

let sanitize_name n =
  let s, cnt = split_name n.hint_name in
  { n with
    hint_name = s
  ; hint_cnt =
      (match n.hint_cnt with
      | None -> cnt
      | Some old_cnt -> (
        match cnt with
        | None -> n.hint_cnt
        | Some name_cnt ->
          Some
            (int_of_string (string_of_int name_cnt ^ string_of_int old_cnt))))
  }

let inc_hint_cnt : int option -> int option = function
  | None -> Some 1
  | Some k -> Some (k + 1)

let gen_fresh_name ns n =
  let rec next_unused y xs =
    if List.mem y xs then next_unused (inc_hint_cnt y) xs else y
  in
  let cnts =
    List.filter_map
      (fun n' ->
        let open Option in
        String.equal n'.hint_name n.hint_name
        |> of_bool $> Fun.const n'.hint_cnt)
      ns
  in
  { n with hint_cnt = next_unused n.hint_cnt cnts }

let max_usage ctx s =
  let same_head s name = String.equal name.hint_name s in
  let max' k name = max k name.hint_cnt in
  match List1.of_list (List.filter (same_head s) ctx) with
  | None ->
    dprintf (fun p ->
        p.fmt "[max_usage] @[<v 2>%s is unused in@,@[%a@]@]" s pp_list ctx);
    `unused
  | Some names ->
    let k = List1.fold_left (fun x -> x.hint_cnt) max' names in
    dprintf (fun p ->
        p.fmt "[max_usage] @[<v 2>%s is USED, k = %a in@,@[%a@]@]" s
          (Option.show Format.pp_print_int)
          k pp_list ctx);
    `used k

type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | SVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of t
  | SomeString of string

let mk_name ?(location = Location.ghost) ?(modules = []) : name_guide -> t =
  let mk_name_helper (nm : string) : t =
    let hint_name, hint_cnt = split_name nm in
    { modules; hint_name; hint_cnt; location }
  in
  function
  (* If no {!name} is given, create a new unique {!name}. This prevents the
     problem that when a {!Store.Typ.entry} or {!Store.Term.entry} is looked
     up, we never have to compare a {!string option}. This prevents the case
     where two entries appear to refer to the same name because {!None} =
     {!None}. *)
  | MVarName (Some vGen)
  | SVarName (Some vGen)
  | PVarName (Some vGen)
  | BVarName (Some vGen) -> mk_name_helper (vGen ())
  | MVarName None | SVarName None ->
    mk_name_helper (Gensym.MVarData.gensym ())
  | PVarName None -> mk_name_helper ("#" ^ Gensym.VarData.gensym ())
  | BVarName None | NoName -> mk_name_helper (Gensym.VarData.gensym ())
  | SomeName x -> sanitize_name x
  | SomeString x -> mk_name_helper x

let mk_blank = function
  | Some location -> mk_name ~location (SomeString "_")
  | None -> mk_name (SomeString "_")

include (
  Eq.Make (struct
    type nonrec t = t

    let equal n1 n2 = String.equal (string_of_name n1) (string_of_name n2)
  end) :
    Eq.EQ with type t := t)

let hash = Fun.(render_name >> Hashtbl.hash)
