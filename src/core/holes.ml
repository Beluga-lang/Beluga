(* module Holes *)

open Support

module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

type lf_hole_info =
  { cPsi : LF.dctx
  ; lfGoal : LF.tclo
  ; mutable lfSolution : LF.nclo option
  }

type comp_hole_info =
  { cG : Comp.gctx
  ; compGoal : Comp.typ * LF.msub
  ; mutable compSolution : Comp.exp_chk option
  }

(* Define some singletons for selecting comp or LF holes. *)
type _ hole_info =
  | LFInfo : lf_hole_info hole_info
  | CompInfo : comp_hole_info hole_info

type 'a hole =
  { loc : Syntax.Loc.t
  ; name : HoleId.name
    (** "Context Delta", for metavariables. *)
  ; cD : LF.mctx
    (** information specific to the hole type. *)
  ; info : 'a
  }

let compare_loc {loc = l1; _} {loc = l2; _} = Loc.compare_start l1 l2

type some_hole =
  | Exists : 'a hole_info * 'a hole -> some_hole


let to_lf_hole : some_hole -> lf_hole_info hole option =
  function
  | Exists (LFInfo, h) -> Some h
  | _ -> None

let to_comp_hole : some_hole -> comp_hole_info hole option =
  function
  | Exists (CompInfo, h) -> Some h
  | _ -> None

let is_solved : some_hole -> bool =
  fun (Exists (w, h)) ->
  match w, h with
  | CompInfo, { info = { compSolution = Some _; _ }; _ } -> true
  | LFInfo, { info = { lfSolution = Some _; _ }; _ } -> true
  | _ -> false

let is_unsolved : some_hole -> bool =
  fun h -> not (is_solved h)

type lookup_strategy =
  { repr : string
  ; action : unit -> (HoleId.t * some_hole) option
  }

type error =
  | InvalidHoleIdentifier of string
  | NoSuchHole of lookup_strategy
  | NameShadowing of
      string (* problematic name *)
      * Loc.t (* location of existing hole *)
  | UnsolvedHole of HoleId.name * HoleId.t

let string_of_lookup_strategy : lookup_strategy -> string = function
  | { repr; _ } -> repr

let print_lookup_strategy ppf (s : lookup_strategy) : unit =
  let open Format in
  fprintf ppf "%s" (string_of_lookup_strategy s)

exception Error of Loc.t * error

let throw loc e = raise (Error (loc, e))

let format_error ppf : error -> unit =
  let open Format in
  function
  | InvalidHoleIdentifier s ->
     fprintf ppf "Invalid hole identifier: %s" s
  | NoSuchHole s ->
     fprintf ppf "No such hole %a" print_lookup_strategy s
  | NameShadowing (s, loc) ->
     fprintf ppf "Hole with name %s already defined at %a"
       s
       Loc.print loc
  | UnsolvedHole (name, id) ->
     fprintf ppf "Hole %s is unsolved"
       (HoleId.string_of_name_or_id (name, id))

let _ =
  Error.register_printer'
    (function
     | Error (loc, e) ->
        Some (Error.print_with_location loc (fun ppf -> format_error ppf e))
     | _ -> None)

let hole_is_named (h : some_hole) : bool =
  let Exists (_, h) = h in
  HoleId.is_anonymous h.name

let (holes : (HoleId.t, some_hole) Hashtbl.t) = Hashtbl.create 32

let find (p : some_hole -> bool) : (HoleId.t * some_hole) option =
  let f k h m =
    let open Maybe in
    m <|> lazy (p h |> of_bool &> pure (k, h))
  in
  Hashtbl.fold f holes (lazy None)
  |> Lazy.force

let lookup (name : string) : (HoleId.t * some_hole) option =
  let matches_name =
    function
    | { name = HoleId.Named n; _ } -> n = name
    | _ -> false in
  find (fun (Exists (_, h)) -> matches_name h)

let count () : int = Hashtbl.length holes
let none () : bool = 0 = count ()

(** More holes **)

(* loc -> loc' -> bool : is loc' within loc? *)
let loc_within (loc : Loc.t) (loc' : Loc.t) : bool =
  (* To check this, it suffices to look at the start offset and end offset.
   * Specifically, loc' needs to start after loc and end before loc.
   *)
  Loc.start_offset loc' >= Loc.start_offset loc && Loc.stop_offset loc' <= Loc.stop_offset loc

(* removes all holes located within the given loc (e.g. of a function being shadowed) *)
let destroy_holes_within loc =
  Hashtbl.filter_map_inplace
    (fun k (Exists (w, h)) ->
      let open Maybe in
      not (loc_within loc h.loc)
      |> of_bool
      &> pure (Exists (w, h)))
    holes

(** Checks that the given hole's name is not already stored. *)
let check_hole_uniqueness (Exists (_, h) : some_hole) : unit =
  let open HoleId in
  match h.name with
  | Anonymous -> () (* anonymous holes never overlap existing holes *)
  | Named s ->
     match lookup s with
     | None -> ()
     | Some (_, Exists (_, h')) ->
        throw h.loc (NameShadowing (s, h'.loc))

let by_id (i : HoleId.t) : lookup_strategy =
  { repr =
      begin
        let open Format in
        fprintf str_formatter "by id '%a'" HoleId.fmt_ppr_id i ;
        flush_str_formatter ()
      end
  ; action =
      fun () ->
      let open Maybe in
      Hashtbl.find_opt holes i
      $> fun h -> (i, h)
  }

module Snapshot =
  Set.Make
    (struct
      type t = HoleId.t
      let compare = HoleId.compare
    end)

(** Represents a collection of holes at a particular time.
    Essentially, this is a set of hole ids.
 *)
type snapshot = Snapshot.t

let get_snapshot () : snapshot =
  let f k _ s = Snapshot.add k s in
  Hashtbl.fold f holes Snapshot.empty

(** Gets all the holes that were added since the given snapshot. *)
let holes_since (past : snapshot) : (HoleId.t * some_hole) list =
  let f k =
    Hashtbl.find_opt holes k
    |> Maybe.get' (Error.Violation "membership of hole is guaranteed by snapshot")
    |> Pair.left k
  in
  let present = get_snapshot () in
  Snapshot.diff present past
  |> Snapshot.elements
  |> List.map f

let catch f =
  let s = get_snapshot () in
  let x = f () in
  let hs = holes_since s in
  (hs, x)

let by_name (name : string) : lookup_strategy =
  { repr = Printf.sprintf "by name '%s'" name
  ; action = fun () -> lookup name
  }

(* All the work of getting the hole is inside the strategy, so we
 * just run it. *)
let get (s : lookup_strategy) : (HoleId.t * some_hole) option = s.action ()

let unsafe_get (s : lookup_strategy) : HoleId.t * some_hole =
  match s.action () with
  | None -> throw Loc.ghost (NoSuchHole s)
  | Some h -> h

let harpoon_subgoals = DynArray.create ()

let add_harpoon_subgoal = DynArray.add harpoon_subgoals

let get_harpoon_subgoals () = DynArray.to_list harpoon_subgoals

let clear () =
  Hashtbl.clear holes;
  DynArray.clear harpoon_subgoals

let list () =
  let f k h l = (k, h) :: l in
  Hashtbl.fold f holes []
  |> List.sort (fun (_, (Exists (_, h1))) (_, (Exists (_, h2))) -> compare_loc h1 h2)

let parse_lookup_strategy (s : string) : lookup_strategy option =
  try
    int_of_string s |> HoleId.of_int |> by_id |> Maybe.pure
  with
  | Failure _ -> Some (by_name s)

let unsafe_parse_lookup_strategy loc (s : string) : lookup_strategy =
  match parse_lookup_strategy s with
  | Some s -> s
  | None -> throw loc (InvalidHoleIdentifier s)

(* instantiate a counter for hole IDs;
   this module is kept private to Holes *)
module ID = HoleId.Make (Module.Unit)

let allocate () = ID.next ()
let assign id h =
  match Hashtbl.find_opt holes id with
  | Some _ ->
     Error.violation "duplicate hole assignment"
  | None ->
     check_hole_uniqueness h;
     Hashtbl.add holes id h
