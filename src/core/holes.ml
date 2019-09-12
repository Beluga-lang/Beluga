(* module Holes *)

open Support

module P = Pretty.Int.DefaultPrinter
module Loc = Syntax.Loc
module LF = Syntax.Int.LF
module Comp = Syntax.Int.Comp

type hole_id = int

let string_of_hole_id = string_of_int

let next_key = ref 0
let get_next_key () =
  let x = !next_key in
  incr next_key;
  x

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

let string_of_name_or_id : hole_name * hole_id -> string = function
  | Anonymous, i -> string_of_hole_id i
  | Named s, _ -> s

type lf_hole_info =
  { cPsi : LF.dctx
  ; lfGoal : LF.tclo
  }

type comp_hole_info =
  { cG : Comp.gctx
  ; compGoal : Comp.typ * LF.msub
  }

type hole_info =
  | LfHoleInfo of lf_hole_info
  | CompHoleInfo of comp_hole_info

type hole =
  { loc : Syntax.Loc.t
  ; name : hole_name
    (** "Context Delta", for metavariables. *)
  ; cD : LF.mctx
    (** information specific to the hole type. *)
  ; info : hole_info
  }

let is_lf_hole h = match h.info with
  | LfHoleInfo _ -> true
  | _ -> false

let is_comp_hole h = match h.info with
  | CompHoleInfo _ -> true
  | _ -> false

type lookup_strategy =
  { repr : string
  ; action : unit -> (hole_id * hole) option
  }

type error =
  | InvalidHoleIdentifier of string
  | NoSuchHole of lookup_strategy

let string_of_lookup_strategy : lookup_strategy -> string = function
  | { repr; _ } -> repr

let print_lookup_strategy ppf (s : lookup_strategy) : unit =
  let open Format in
  fprintf ppf "%s" (string_of_lookup_strategy s)

exception Error of error

let throw e = raise (Error e)

let format_error ppf : error -> unit =
  let open Format in
  function
  | InvalidHoleIdentifier s ->
     fprintf ppf "Invalid hole identifier: %s" s
  | NoSuchHole s ->
     fprintf ppf "No such hole %a" print_lookup_strategy s

let _ =
  Error.register_printer'
    (function
     | Error e -> Some (Error.print (fun ppf -> format_error ppf e))
     | _ -> None)

let hole_is_named (h : hole) : bool =
  match h.name with
  | Anonymous -> false
  | Named _ -> true

let (holes : (hole_id, hole) Hashtbl.t) = Hashtbl.create 32

let find (p : hole -> bool) : (hole_id * hole) option =
  let f k h m =
    let open Maybe in
    m <|> lazy (p h |> of_bool &> pure (k, h))
  in
  Hashtbl.fold f holes (lazy None)
  |> Lazy.force

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
    (fun k h ->
      let open Maybe in
      not (loc_within loc h.loc)
      |> of_bool
      &> pure h)
    holes

let add (h : hole) =
  let x = get_next_key () in
  Hashtbl.add holes x h;
  x

let iterMctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list =
  let (_, sub) = tA in
  let rec aux acc c = function
    | LF.Empty -> acc
    | LF.Dec (cD', LF.Decl(n, LF.ClTyp (LF.MTyp tA', cPsi'), LF.No))
    | LF.Dec (cD', LF.Decl(n, LF.ClTyp (LF.PTyp tA', cPsi'), LF.No))->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        let tA' = Whnf.cnormTyp (tA', LF.MShift c) in
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', sub);
        aux (n::acc) (c+1) cD'
      with | _ -> aux acc (c+1) cD' end
    | LF.Dec (cD', _) -> aux acc (c + 1) cD'
  in aux [] 1 cD

let iterDctx (cD : LF.mctx) (cPsi : LF.dctx) (tA : LF.tclo) : Id.name list =
  let rec aux acc = function
    | LF.DDec(cPsi', LF.TypDecl(n, tA')) ->
      begin try
        Unify.StdTrail.resetGlobalCnstrs ();
        Unify.StdTrail.unifyTyp cD cPsi tA (tA', LF.EmptySub);
        aux (n::acc) cPsi'
      with | _ -> aux acc cPsi' end
    | LF.DDec(cPsi', _) -> aux acc cPsi'
    | _ -> acc
  in
    aux [] cPsi

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

let replicate n c = String.init n (Misc.const c)
let thin_line = replicate 80 '_'
let thin_line ppf () = Format.fprintf ppf "%s" thin_line

let print ppf (i, {loc; name; cD; info}) : unit =
  let open Format in
  (* First, we do some preparations. *)
  (* Normalize the LF and computational contexts as well as the goal type. *)
  let cD = Whnf.normMCtx cD in
  (* Now that we've prepped all the things to format, we can prepare the message. *)
  (* We do this by preparing different *message components* which are
   * assembled into the final message. *)

  fprintf ppf "@[<v>";

  (* 1. The 'hole identification component' contains the hole name (if any) and its number. *)
  let print_hole_name ppf = function
    | Anonymous -> fprintf ppf "<anonymous>"
    | Named s -> fprintf ppf "?%s" s
  in
  fprintf ppf
    "@[<hov>%a:@ Hole number %d, %a@]@,"
    Loc.print loc
    i
    print_hole_name name;
  fprintf ppf "@,";
  (* thin_line ppf (); *)

  (* 2. The meta-context information. *)
  fprintf ppf "Meta-context:@,  @[<v>%a@]@,"
    (P.fmt_ppr_lf_mctx ~sep: pp_print_cut P.l0) cD;
  fprintf ppf "@,";
  (* thin_line ppf (); *)

  let plural ppf = function
    | true -> fprintf ppf "s"
    | false -> ()
  in

  (* The remainder of the formatting hinges on whether we're printing
     an LF hole or a computational hole.
   *)
  begin match info with
  | LfHoleInfo { cPsi; lfGoal } ->
     let lfGoal' = Whnf.normTyp lfGoal in
     let cPsi = Whnf.normDCtx cPsi in

     (* 3. format the LF context information *)
     fprintf ppf "LF Context:@,  @[<v>%a@]@,"
       (P.fmt_ppr_lf_dctx cD P.l0) cPsi;
     fprintf ppf "@,";

     (* 4. Format the goal. *)
     thin_line ppf ();
     fprintf ppf "@[Goal:@ %a@]" (P.fmt_ppr_lf_typ cD cPsi P.l0) lfGoal';

     (* 5. The in-scope variables that have the goal type, if any *)
     let suggestions =
       (* Need to check both the LF context and the meta-variable context. *)
       iterMctx cD cPsi lfGoal @ iterDctx cD cPsi lfGoal
     in
     if Misc.List.nonempty suggestions then
       fprintf ppf
         "@,@,Variable%a of this type: @[<h>%a@]"
         plural (List.length suggestions = 1)
         (pp_print_list ~pp_sep: Fmt.comma Id.print) suggestions

  | CompHoleInfo { cG; compGoal = (tau, theta) } ->
     let cG = Whnf.normCtx cG in
     let goal = Whnf.cnormCTyp (tau, theta) in
     (* 3. The (computational) context information. *)
     fprintf ppf "Computation context:@,  @[<v>%a@]@,"
       (P.fmt_ppr_cmp_gctx cD P.l0) cG;
     fprintf ppf "@,";

     (* 4. The goal type, i.e. the type of the hole. *)
     fprintf ppf "@[Goal:@ %a@]"
       (P.fmt_ppr_cmp_typ cD P.l0) goal;

     (* Collect a list of variables that already have the goal type. *)
     let suggestions = iterGctx cD cG (tau, theta) in
     if Misc.List.nonempty suggestions then
       fprintf ppf
         "@,@,Variable%a of this type: @[<h>%a@]"
         plural (List.length suggestions = 1)
         (pp_print_list ~pp_sep: Fmt.comma Id.print) suggestions
  end;
  fprintf ppf "@]"

let by_id (i : hole_id) : lookup_strategy =
  { repr = Printf.sprintf "by id '%d'" i
  ; action =
      fun () ->
      let open Maybe in
      Hashtbl.find_opt holes i
      $> fun h -> (i, h)
  }

module Snapshot =
  Set.Make
    (struct
      type t = hole_id
      let compare = compare
    end)

(** Represents a collection of holes at a particular time.
    Essentially, this is a set of hole ids.
 *)
type snapshot = Snapshot.t

let get_snapshot () : snapshot =
  let f k _ s = Snapshot.add k s in
  Hashtbl.fold f holes Snapshot.empty

(** Gets all the holes that were added since the given snapshot. *)
let holes_since (past : snapshot) : (hole_id * hole) list =
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
  | None -> throw (NoSuchHole s)
  | Some h -> h

let clear () = Hashtbl.clear holes

let list () =
  let f k h l = (k, h) :: l in
  Hashtbl.fold f holes []

let parse_lookup_strategy (s : string) : lookup_strategy option =
  try
    Some (by_id (int_of_string s))
  with
  | Failure _ -> Some (by_name s)

let unsafe_parse_lookup_strategy (s : string) : lookup_strategy =
  match parse_lookup_strategy s with
  | Some s -> s
  | None -> throw (InvalidHoleIdentifier s)
