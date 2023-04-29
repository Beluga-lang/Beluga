open Support.Equality
open Support
open Beluga_syntax
module LF = Synint.LF
module Comp = Synint.Comp

[@@@warning "+A-4-44"]

type lf_hole_info =
  { cPsi : LF.dctx
  ; lfGoal : LF.tclo
  ; mutable lfSolution : LF.nclo option
  }

type comp_hole_info =
  { cG : Comp.gctx
  ; compGoal : Comp.typ * LF.msub
  ; mutable compSolution : Comp.exp option
  }

(* Define some singletons for selecting comp or LF holes. *)
type _ hole_info =
  | LFInfo : lf_hole_info hole_info
  | CompInfo : comp_hole_info hole_info

type 'a hole =
  { location : Location.t
  ; name : HoleId.name
  ; cD : LF.mctx  (** "Context Delta", for metavariables. *)
  ; info : 'a  (** information specific to the hole type. *)
  }

let compare_hole_location h1 h2 =
  Location.compare_start h1.location h2.location

type some_hole = Exists : 'a hole_info * 'a hole -> some_hole

let to_lf_hole : some_hole -> lf_hole_info hole option = function
  | Exists (LFInfo, h) -> Option.some h
  | Exists (_, _) -> Option.none

let to_comp_hole : some_hole -> comp_hole_info hole option = function
  | Exists (CompInfo, h) -> Option.some h
  | Exists (_, _) -> Option.none

let is_solved : some_hole -> bool =
 fun (Exists (w, h)) ->
  match (w, h) with
  | CompInfo, { info = { compSolution = Option.Some _; _ }; _ } -> true
  | LFInfo, { info = { lfSolution = Option.Some _; _ }; _ } -> true
  | _ -> false

let is_unsolved : some_hole -> bool = fun h -> Bool.not (is_solved h)

type lookup_strategy =
  { repr : string
  ; action : unit -> (HoleId.t * some_hole) option
  }

exception Invalid_hole_identifier of string

exception No_such_hole of lookup_strategy

exception Name_shadowing of string

let string_of_lookup_strategy ({ repr; _ } : lookup_strategy) : string = repr

let print_lookup_strategy ppf (s : lookup_strategy) : unit =
  Format.fprintf ppf "%s" (string_of_lookup_strategy s)

let () =
  Error.register_exception_printer (function
    | Invalid_hole_identifier s ->
        Format.dprintf "Invalid hole identifier: %s." s
    | No_such_hole s ->
        Format.dprintf "No such hole %a." print_lookup_strategy s
    | Name_shadowing s ->
        Format.dprintf "Hole with name %s already defined." s
    | exn -> Error.raise_unsupported_exception_printing exn)

let hole_is_named (h : some_hole) : bool =
  let (Exists (_, h)) = h in
  HoleId.is_anonymous h.name

let (holes : (HoleId.t, some_hole) Hashtbl.t) = Hashtbl.create 32

let find (p : some_hole -> bool) : (HoleId.t * some_hole) option =
  Seq.find (fun (_key, hole) -> p hole) (Hashtbl.to_seq holes)

let lookup (name : string) : (HoleId.t * some_hole) option =
  let matches_name = function
    | { name = HoleId.Named n; _ } -> String.equal n name
    | { name = HoleId.Anonymous; _ } -> false
  in
  find (fun (Exists (_, h)) -> matches_name h)

let count () : int = Hashtbl.length holes

let none () : bool = 0 = count ()

(** More holes **)

(* loc -> loc' -> bool : is loc' within loc? *)
let loc_within (loc : Location.t) (loc' : Location.t) : bool =
  (* To check this, it suffices to look at the start offset and end offset.
     Specifically, loc' needs to start after loc and end before loc. *)
  Location.start_offset loc' >= Location.start_offset loc
  && Location.stop_offset loc' <= Location.stop_offset loc

(* removes all holes located within the given loc (e.g. of a function being
   shadowed) *)
let destroy_holes_within loc =
  Hashtbl.filter_map_inplace
    (fun _key (Exists (w, h)) ->
      let open Option in
      (not (loc_within loc h.location)) |> of_bool &> some (Exists (w, h)))
    holes

(** Checks that the given hole's name is not already stored. *)
let check_hole_uniqueness (Exists (_, h) : some_hole) : unit =
  let open HoleId in
  match h.name with
  | Anonymous -> () (* anonymous holes never overlap existing holes *)
  | Named s -> (
      match lookup s with
      | Option.None -> ()
      | Option.Some (_, Exists (_, h')) ->
          Error.raise_at2 h.location h'.location (Name_shadowing s))

let by_id (i : HoleId.t) : lookup_strategy =
  { repr = Format.asprintf "by id '%a'" HoleId.fmt_ppr_id i
  ; action =
      (fun () ->
        let open Option in
        Hashtbl.find_opt holes i $> fun h -> (i, h))
  }

module Snapshot = Set.Make (struct
  type t = HoleId.t

  let compare = HoleId.compare
end)

(** Represents a collection of holes at a particular time. Essentially, this
    is a set of hole ids. *)
type snapshot = Snapshot.t

let get_snapshot () : snapshot =
  let f k _ s = Snapshot.add k s in
  Hashtbl.fold f holes Snapshot.empty

(** Gets all the holes that were added since the given snapshot. *)
let holes_since (past : snapshot) : (HoleId.t * some_hole) list =
  let f k =
    match Hashtbl.find_opt holes k with
    | Option.None ->
        Error.raise_violation "membership of hole is guaranteed by snapshot"
    | Option.Some x -> (k, x)
  in
  let present = get_snapshot () in
  Snapshot.diff present past |> Snapshot.elements |> List.map f

let catch f =
  let s = get_snapshot () in
  let x = f () in
  let hs = holes_since s in
  (hs, x)

let by_name (name : string) : lookup_strategy =
  { repr = Printf.sprintf "by name '%s'" name
  ; action = (fun () -> lookup name)
  }

(* All the work of getting the hole is inside the strategy, so we
 * just run it. *)
let get (s : lookup_strategy) : (HoleId.t * some_hole) option = s.action ()

let unsafe_get (s : lookup_strategy) : HoleId.t * some_hole =
  match s.action () with
  | None -> Error.raise (No_such_hole s)
  | Some h -> h

let harpoon_subgoals : Comp.open_subgoal DynArray.t =
  DynArray.create ()

let add_harpoon_subgoal = DynArray.add harpoon_subgoals

let get_harpoon_subgoals () = DynArray.to_list harpoon_subgoals

let clear () =
  Hashtbl.clear holes;
  DynArray.clear harpoon_subgoals

let list () =
  Hashtbl.fold (fun k h l -> (k, h) :: l) holes []
  |> List.sort (fun (_, Exists (_, h1)) (_, Exists (_, h2)) ->
         compare_hole_location h1 h2)

let parse_by_id_lookup_strategy (s : string) : lookup_strategy option =
  try
    let hold_id = HoleId.of_int (int_of_string s) in
    Option.some (by_id hold_id)
  with
  | Failure _ -> Option.none

let parse_lookup_strategy (s : string) : lookup_strategy option =
  match parse_by_id_lookup_strategy s with
  | Option.None -> Option.some (by_name s)
  | x -> x

let unsafe_parse_lookup_strategy location (s : string) : lookup_strategy =
  match parse_lookup_strategy s with
  | Option.Some s -> s
  | Option.None -> Error.raise_at1 location (Invalid_hole_identifier s)

(* instantiate a counter for hole IDs; this module is kept private to
   Holes *)
module ID = HoleId.Make ()

let allocate () = ID.next ()

let assign id h =
  match Hashtbl.find_opt holes id with
  | Option.Some _ -> Error.raise_violation "duplicate hole assignment"
  | Option.None ->
      check_hole_uniqueness h;
      Hashtbl.add holes id h
