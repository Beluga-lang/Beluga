(* module Holes *)

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

type hole_id = int

type hole_name =
  | Anonymous
  | Named of string

let name_of_option : string option -> hole_name = function
  | Some name -> Named name
  | None -> Anonymous

let option_of_name : hole_name -> string option = function
  | Anonymous -> None
  | Named s -> Some s

let string_of_name : hole_name -> string = function
  | Anonymous -> ""
  | Named s -> s

type hole =
  { loc : Syntax.Loc.t;
    name : hole_name;
    (** "Context Delta", for LF types. *)
    cD : LF.mctx;
    (** "Context Gamma", for computation types. *)
    cG : Comp.gctx;
    goal : Comp.typ * LF.msub;
  }

type lookup_strategy =
  { repr : string
  ; action : unit -> (hole_id * hole) option
  }

let string_of_lookup_strategy : lookup_strategy -> string = function
  | { repr; _ } -> repr

exception NoSuchHole of lookup_strategy

let hole_is_named (h : hole) : bool =
  match h.name with
  | Anonymous -> false
  | Named _ -> true

let (holes : hole DynArray.t) = DynArray.create ()

let (staged_holes : hole DynArray.t) = DynArray.create ()

let index_of (haystack : 'a DynArray.t) (f : 'a -> bool) : int option =
  try
    Some (DynArray.index_of f haystack)
  with
    Not_found -> None

let find_common (haystack : 'a DynArray.t) (f : 'a -> bool)  : (int * 'a) option =
  match index_of haystack f with
  | None -> None
  | Some i -> Some (i, DynArray.get haystack i)

let find (f : hole -> bool) : (int * hole) option =
  find_common holes f

let find_staged (f : hole -> bool) : (int * hole) option =
  find_common staged_holes f

let none () : bool = DynArray.empty holes

let stage : hole -> unit = DynArray.add staged_holes

let ( ++ ) f g = function x -> f (g x)

let ctypDeclToString cD ctypDecl =
  P.fmt_ppr_lf_ctyp_decl ~printing_holes:true cD Pretty.std_lvl Format.str_formatter ctypDecl ;
  Format.flush_str_formatter ()

let isExplicit = function
  | LF.Decl(_, _, dep) ->
      begin match dep with
        | LF.No -> true
        | LF.Maybe -> false
	| LF.Inductive -> false
      end
  | _ -> true

 let mctxToString =
  let shift = "\t" in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, ctypDecl) when (isExplicit ctypDecl || !Pretty.Control.printImplicit) ->
      "\n" ^ shift ^ ctypDeclToString LF.Empty ctypDecl
    | LF.Dec (cD, ctypDecl) when (isExplicit ctypDecl || !Pretty.Control.printImplicit)->
      let s = toString cD in
      s ^ "\n" ^ shift ^ ctypDeclToString cD ctypDecl
    | LF.Dec (cD, _ ) -> toString cD
  in toString ++ Whnf.normMCtx

let gctxToString cD =
  let shift = "\t" in
  let rec toString = function
    | LF.Empty ->
      "."
    | LF.Dec (LF.Empty, Comp.CTypDecl (n, tau, flag )) ->
      let s =  if flag then "*" else "" in 
      "\n" ^ shift ^ (Id.string_of_name n) ^ s ^ ": " ^ P.compTypToString cD tau
    | LF.Dec (cG, Comp.CTypDecl (n, tau,flag)) ->
      let s =  if flag then "*" else "" in 
      toString cG ^ "\n" ^ shift ^ (Id.string_of_name n) ^ s ^ ": " ^ P.compTypToString cD tau
  in toString ++ Whnf.normCtx

(** More holes **)

(* loc -> loc' -> bool : is loc' within loc? *)
let loc_within (loc : Loc.t) (loc' : Loc.t) : bool =
  (* To check this, it suffices to look at the start offset and end offset.
   * Specifically, loc' needs to start after loc and end before loc.
   *)
  Loc.start_off loc' >= Loc.start_off loc && Loc.stop_off loc' <= Loc.stop_off loc

(* removes all holes located within the given loc (e.g. of a function being shadowed) *)
let destroy_holes_within loc =
  DynArray.filter (fun {loc = loc'; _} -> not (loc_within loc loc')) holes

let commit () =
  DynArray.append (DynArray.copy staged_holes) holes;
  DynArray.clear staged_holes

let clear_staged () =
  DynArray.clear staged_holes

(* A helper for implementing at and staged_at. *)
let matches_loc loc' {loc; _} = loc = loc'

(* Should only be called with the loc of a hole *)
let at (loc : Syntax.Loc.t) : (hole_id * hole) option =
  find (matches_loc loc)

let staged_at (loc : Syntax.Loc.t) : (hole_id * hole) option =
  find_staged (matches_loc loc)

(** Transforms an element of a dynamic array at a specific index with a provided function. *)
let transform_at (haystack : 'a DynArray.t) (i : hole_id) (f : 'a -> 'a) : unit =
  let e = DynArray.get haystack i in DynArray.set haystack i (f e)

let set_staged_hole_pos i l =
  transform_at staged_holes i (fun h -> { h with loc = l })

let iterGctx (cD : LF.mctx) (cG : Comp.gctx) (ttau : Comp.tclo) : Id.name list =
  let rec aux acc = function
    | LF.Empty -> acc
    | LF.Dec (cG', Comp.CTypDecl(n, tau', _ )) ->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        Unify.StdTrail.unifyCompTyp cD ttau (tau', LF.MShift 0);
        aux (n::acc) cG'
      with | _ -> aux acc cG' end
    | LF.Dec (cG', _) -> aux acc cG'
  in aux [] cG

let replicate n c = String.init n (fun _ -> c)
let thin_line = replicate 80 '_'
let thick_line = replicate 80 '='

let format_hole (i : hole_id) {loc; name; cD; cG; goal = (tau, theta)} : string=
  (* First, we do some preparations. *)
  (* Normalize the LF and computational contexts as well as the goal type. *)
  let cD = Whnf.normMCtx cD in
  let cG = Whnf.normCtx cG in
  let goal = Whnf.cnormCTyp (tau, theta) in
  (* Collect a list of variables that already have the goal type. *)
  let suggestions = iterGctx cD cG (tau, theta) in
  let plural b = if b then "" else "s" in
  let loc_string = Loc.to_string loc in
  (* Now that we've prepped all the things to format, we can prepare the message. *)
  (* We do this by preparing different *message components* which are
   * assembled into the final message. *)

  (* 1. The 'hole identification component' contains the hole name (if any) and its number. *)
  let hole_id =
    let hole_name =
      match name with
      | Anonymous -> ""
      | Named s -> Format.sprintf ", %s" s in
    Format.sprintf "Hole number %d%s\n%s\n%s" i hole_name loc_string thin_line in

  (* 2. The meta-context information. *)
  let meta_ctx_info =
    Format.sprintf "Meta-context: %s\n%s" (mctxToString cD) thin_line in

  (* 3. The (computational) context information. *)
  let comp_ctx_info =
    Format.sprintf "Context: %s\n%s" (gctxToString cD cG) thick_line in

  (* 4. The goal type, i.e. the type of the hole. *)
  let goal_type =
    Format.sprintf "Goal: %s" (P.compTypToString cD goal) in

  (* 5. The in-scope variables of the correct type. *)
  let suggestions_str =
    let s = String.concat ", " (List.map Id.string_of_name suggestions) in
    let p = plural (List.length suggestions = 1) in
    Format.sprintf "Variable%s of this type: %s" p s in

  (* a helper *)
  let null =
    function
    | [] -> true
    | _ :: _ -> false in

  (* Finally, we can form the output. *)
  String.concat "\n"
    ( hole_id :: meta_ctx_info :: comp_ctx_info :: goal_type ::
        if null suggestions then [] else [suggestions_str] )

let by_id (i : hole_id) : lookup_strategy =
  { repr = Printf.sprintf "by id '%d'" i
  ; action =
      fun () ->
      if i < DynArray.length holes then
        Some (i, DynArray.get holes i)
      else
        None
  }

let lookup (name : string) : (hole_id * hole) option =
  let matches_name =
    function
    | { name = Named n; _ } -> n = name
    | _ -> false in
  find matches_name

let by_name (name : string) : lookup_strategy =
  { repr = Printf.sprintf "by name '%s'" name
  ; action = fun () -> lookup name
  }

(* All the work of getting the hole is inside the strategy, so we
 * just run it. *)
let get (s : lookup_strategy) : (hole_id * hole) option = s.action ()

let unsafe_get (s : lookup_strategy) : hole_id * hole =
  match s.action () with
  | None -> raise (NoSuchHole s)
  | Some h -> h

let count () = DynArray.length holes

let clear () = DynArray.clear holes

let list () = DynArray.to_list holes

let parse_lookup_strategy (s : string) : lookup_strategy option =
  try
    Some (by_id (int_of_string s))
  with
  | Failure _ -> Some (by_name s)

let unsafe_parse_lookup_strategy (s : string) : lookup_strategy =
  match parse_lookup_strategy s with
  | Some s -> s
  | None -> failwith ("Invalid hole identifier: " ^ s)
