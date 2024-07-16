[@@@warning "+A-4-32-44"]

open! Support
open Beluga
open Beluga_syntax.Syncom
open Beluga_syntax.Synint

(** {1 Computing Dependency Call Graphs for Theorems}

    This module provides functions for computing a dependency call graph for
    theorems in a reconstructed Beluga signature. This call graph is built by
    traversing the entire signature. *)

(** {2 Traversing the Structure of Theorems} *)

(** Record of the IDs of called programs for a given theorem.

    In the call graph structure, each theorem is associated with a calls
    record. Note that a calls record only contains the direct dependencies
    for a theorem. *)
module CallsRecord : sig
  (** The type of calls records. *)
  type t

  (** [create ()] is a new empty calls record. *)
  val create : unit -> t

  val add_program_call : t -> Id.cid_prog -> unit

  val has_program_call : t -> Id.cid_prog -> bool

  (** [iter f r] iteratively applies [f] over the program calls added to [r]. *)
  val iter : (Id.cid_prog -> unit) -> t -> unit

  (** [to_set r] is the set of called program IDs recorded in [r]. *)
  val to_set : t -> Id.Prog.Set.t
end = struct
  type t = { mutable called_programs : Id.Prog.Set.t }

  let create () = { called_programs = Id.Prog.Set.empty }

  let add_program_call calls prog =
    calls.called_programs <- Id.Prog.Set.add prog calls.called_programs

  let has_program_call calls prog =
    Id.Prog.Set.mem prog calls.called_programs

  let iter f calls = Id.Prog.Set.iter f calls.called_programs

  let to_set calls = calls.called_programs
end

type calls_record = CallsRecord.t

(* In order to build the calls record for a theorem, we need to fully
   traverse its structure. Here, we use the internal syntax representation of
   the theorem because the indexing phase already handles name resolution.

   The traversal is achieved using the visitor design pattern: we define a
   collection of mutually recursive functions for each level in the structure
   of a theorem, and add called program IDs to the visitor state as they are
   encountered. *)

(** {3 Signature-Level Theorem Visitor} *)

let rec visit_thm : calls_record -> Comp.thm -> unit =
 fun calls_record -> function
  | Comp.Proof proof -> visit_harpoon_proof calls_record proof
  | Comp.Program program -> visit_exp calls_record program

(** {3 Beluga Program Visitors} *)

and visit_exp : calls_record -> Comp.exp -> unit =
 fun calls_record -> function
  | Comp.Fn (_, _, body) -> visit_exp calls_record body
  | Comp.Fun (_, branches) -> visit_fun_branches calls_record branches
  | Comp.MLam (_, _, body, _) -> visit_exp calls_record body
  | Comp.Tuple (_, elements) -> List2.iter (visit_exp calls_record) elements
  | Comp.LetTuple (_, scrutinee, (_, body)) ->
      visit_exp calls_record scrutinee;
      visit_exp calls_record body
  | Comp.Let (_, scrutinee, (_, body)) ->
      visit_exp calls_record scrutinee;
      visit_exp calls_record body
  | Comp.Box (_, _, _) -> ()
  | Comp.Case (_, _, scrutinee, branches) ->
      visit_exp calls_record scrutinee;
      visit_branches calls_record branches
  | Comp.Impossible (_, scrutinee) -> visit_exp calls_record scrutinee
  | Comp.Hole (_, _, _) -> ()
  | Comp.Var (_, _) -> ()
  | Comp.DataConst (_, _) -> ()
  | Comp.Obs (_, _, _, _) -> ()
  | Comp.Const (_, called_prog) ->
      (* Reached a theorem constant AST node, add the theorem's ID to the
         record of calls *)
      CallsRecord.add_program_call calls_record called_prog
  | Comp.Apply (_, f, argument) ->
      visit_exp calls_record f;
      visit_exp calls_record argument
  | Comp.MApp (_, f, _, _, _) -> visit_exp calls_record f
  | Comp.AnnBox (_, _, _) -> ()

and visit_fun_branches : calls_record -> Comp.fun_branches -> unit =
 fun calls_record -> function
  | Comp.NilFBranch _ -> ()
  | Comp.ConsFBranch (_, (_, _, _, body), branches) ->
      visit_exp calls_record body;
      visit_fun_branches calls_record branches

and visit_branches : calls_record -> Comp.branch list -> unit =
 fun calls_record branches -> List.iter (visit_branch calls_record) branches

and visit_branch : calls_record -> Comp.branch -> unit =
 fun calls_record (Comp.Branch (_, _, _, _, _, body)) ->
  visit_exp calls_record body

(** {3 Harpoon Proof Visitors} *)

and visit_harpoon_proof : calls_record -> Comp.proof -> unit =
 fun calls_record -> function
  | Comp.Incomplete (_, _) -> ()
  | Comp.Command (command, proof) ->
      visit_harpoon_command calls_record command;
      visit_harpoon_proof calls_record proof
  | Comp.Directive directive ->
      visit_harpoon_directive calls_record directive

and visit_harpoon_command : calls_record -> Comp.command -> unit =
 fun calls_record -> function
  | Comp.By (exp, _, _) -> visit_exp calls_record exp
  | Comp.Unbox (scrutinee, _, _, _) -> visit_exp calls_record scrutinee

and visit_harpoon_directive : calls_record -> Comp.directive -> unit =
 fun calls_record -> function
  | Comp.Intros hypothetical ->
      visit_harpoon_hypothetical calls_record hypothetical
  | Comp.Solve solution -> visit_exp calls_record solution
  | Comp.ImpossibleSplit scrutinee -> visit_exp calls_record scrutinee
  | Comp.Suffices (solution, arguments) ->
      visit_exp calls_record solution;
      visit_harpoon_suffices_args calls_record arguments
  | Comp.MetaSplit (scrutinee, _, meta_branches) ->
      visit_exp calls_record scrutinee;
      visit_harpoon_meta_branches calls_record meta_branches
  | Comp.CompSplit (scrutinee, _, branches) ->
      visit_exp calls_record scrutinee;
      visit_harpoon_comp_branches calls_record branches
  | Comp.ContextSplit (scrutinee, _, branches) ->
      visit_exp calls_record scrutinee;
      visit_harpoon_context_branches calls_record branches

and visit_harpoon_hypothetical : calls_record -> Comp.hypothetical -> unit =
 fun calls_record -> function
  | Comp.Hypothetical (_, _, proof) -> visit_harpoon_proof calls_record proof

and visit_harpoon_meta_branches :
    calls_record -> Comp.meta_branch list -> unit =
 fun calls_record meta_branches ->
  List.iter (visit_harpoon_meta_branch calls_record) meta_branches

and visit_harpoon_meta_branch : calls_record -> Comp.meta_branch -> unit =
 fun calls_record (Comp.SplitBranch (_, _, _, hypothetical)) ->
  visit_harpoon_hypothetical calls_record hypothetical

and visit_harpoon_comp_branches :
    calls_record -> Comp.comp_branch list -> unit =
 fun calls_record comp_branches ->
  List.iter (visit_harpoon_comp_branch calls_record) comp_branches

and visit_harpoon_comp_branch : calls_record -> Comp.comp_branch -> unit =
 fun calls_record (Comp.SplitBranch (_, _, _, hypothetical)) ->
  visit_harpoon_hypothetical calls_record hypothetical

and visit_harpoon_context_branches :
    calls_record -> Comp.context_branch list -> unit =
 fun calls_record context_branches ->
  List.iter (visit_harpoon_context_branch calls_record) context_branches

and visit_harpoon_context_branch :
    calls_record -> Comp.context_branch -> unit =
 fun calls_record (Comp.SplitBranch (_, _, _, hypothetical)) ->
  visit_harpoon_hypothetical calls_record hypothetical

and visit_harpoon_suffices_args :
    calls_record -> Comp.suffices_arg list -> unit =
 fun calls_record args ->
  List.iter (visit_harpoon_suffices_arg calls_record) args

and visit_harpoon_suffices_arg : calls_record -> Comp.suffices_arg -> unit =
 fun calls_record (_, _, proof) -> visit_harpoon_proof calls_record proof

(** {2 Traversing the Structure of Beluga Signatures} *)

(** Representation of a dependency call graph for theorems.

    This representation is sparse and implemented by associating each theorem
    ID with a calls record. The set of transitive dependencies for a given
    theorem constant is computed using breadth-first search. *)
module CallGraphState : sig
  exception Unknown_program of Id.cid_prog

  (** The type of call graph states. *)
  type t

  (** [create ()] is a new empty call graph state. *)
  val create : unit -> t

  (** [add_program_calls_record state cid r] adds the association [(cid, r)]
      to [state]. Here, [r] is the set of out-neighbours of [cid] in the call
      graph. *)
  val add_program_calls_record : t -> Id.cid_prog -> calls_record -> unit

  (** [get_immediate_dependencies state cid] is the set of direct
      dependencies of theorem [cid] in [state]. *)
  val get_immediate_dependencies : t -> Id.cid_prog -> Id.Prog.Set.t

  (** [compute_program_call_dependencies state cid] is the set of transitive
      dependencies of theorem [cid] in [state]. That is, it is the set of
      nodes reachable from [cid] in the call graph.

      This is computed using breadth-first search, with memoization to
      optimize runtime. *)
  val compute_program_call_dependencies : t -> Id.cid_prog -> Id.Prog.Set.t

  (** [clear_memoized_call_dependencies state] discards the previously
      computed transitive dependencies of nodes in [state]. This is used
      whenever memoized results have to be invalidated and recomputed from
      scratch. *)
  val clear_memoized_call_dependencies : t -> unit

  (** [set_program_display_name state cid n] sets [n] as the name to use to
      refer to [cid] in [state]. This is only used for pretty-printing the
      call graph. *)
  val set_program_display_name :
    t -> Id.cid_prog -> Qualified_identifier.t -> unit

  (** [lookup_program_display_name state cid] is the name set for [cid] in
      [state] using {!val:set_program_display_name}. *)
  val lookup_program_display_name :
    t -> Id.cid_prog -> Qualified_identifier.t
end = struct
  exception Unknown_program of Id.cid_prog

  type t =
    { program_calls_records : CallsRecord.t Id.Prog.Hashtbl.t
    ; program_call_dependencies : Id.Prog.Set.t Id.Prog.Hashtbl.t
    ; program_display_names : Qualified_identifier.t Id.Prog.Hashtbl.t
    }

  let create () =
    { program_calls_records = Id.Prog.Hashtbl.create 16
    ; program_call_dependencies = Id.Prog.Hashtbl.create 16
    ; program_display_names = Id.Prog.Hashtbl.create 16
    }

  let clear_memoized_call_dependencies state =
    Id.Prog.Hashtbl.clear state.program_call_dependencies

  let add_program_calls_record state cid calls =
    Id.Prog.Hashtbl.add state.program_calls_records cid calls;
    clear_memoized_call_dependencies state

  let get_immediate_dependencies state cid =
    match Id.Prog.Hashtbl.find_opt state.program_calls_records cid with
    | Option.None -> Error.raise (Unknown_program cid)
    | Option.Some calls_record -> CallsRecord.to_set calls_record

  let compute_program_call_dependencies state cid =
    let to_visit = Queue.create () in
    let visited = Stdlib.ref Id.Prog.Set.empty in
    (* Add direct dependencies to the [to_visit] queue *)
    (match Id.Prog.Hashtbl.find_opt state.program_calls_records cid with
    | Option.None -> Error.raise (Unknown_program cid)
    | Option.Some calls_record ->
        CallsRecord.iter (fun x -> Queue.add x to_visit) calls_record);
    while Bool.not (Queue.is_empty to_visit) do
      let current_cid = Queue.pop to_visit in
      if Bool.not (Id.Prog.Set.mem current_cid !visited) then (
        visited := Id.Prog.Set.add current_cid !visited;
        (* Lookup memoization table *)
        match
          Id.Prog.Hashtbl.find_opt state.program_call_dependencies
            current_cid
        with
        | Option.Some call_dependencies ->
            (* The call dependencies are already memoized *)
            visited := Id.Prog.Set.union !visited call_dependencies
        | Option.None -> (
            (* Add the neighbours of the current node to the queue *)
            match
              Id.Prog.Hashtbl.find_opt state.program_calls_records
                current_cid
            with
            | Option.None ->
                (* The program is not part of the call graph *)
                Error.raise (Unknown_program current_cid)
            | Option.Some calls_record ->
                CallsRecord.iter (fun x -> Queue.add x to_visit) calls_record
            ))
    done;
    !visited

  let set_program_display_name state cid identifier =
    Id.Prog.Hashtbl.add state.program_display_names cid identifier

  let lookup_program_display_name state cid =
    match Id.Prog.Hashtbl.find_opt state.program_display_names cid with
    | Option.Some name -> name
    | Option.None -> Error.raise (Unknown_program cid)
end

type state = CallGraphState.t

(** {3 Signature-Level Visitors}

    These visitors are used to construct a call graph starting from a
    reconstructed Beluga signature in internal syntax representation. *)

let rec visit_sgn : state -> Sgn.sgn -> unit =
 fun state sgn -> List1.iter (visit_sgn_file state) sgn

and visit_sgn_file : state -> Sgn.sgn_file -> unit =
 fun state { Sgn.entries; _ } -> List.iter (visit_sgn_entry state []) entries

and visit_sgn_entry : state -> Identifier.t list -> Sgn.entry -> unit =
 fun state namespaces -> function
  | Sgn.Declaration { declaration; _ } ->
      visit_sgn_declaration state namespaces declaration
  | Sgn.Pragma _
  | Sgn.Comment _ ->
      ()

and visit_sgn_declaration : state -> Identifier.t list -> Sgn.decl -> unit =
 fun state namespaces -> function
  | Sgn.Theorem { cid; body; identifier; _ } ->
      let calls_record = CallsRecord.create () in
      visit_thm calls_record body;
      CallGraphState.add_program_calls_record state cid calls_record;
      let qualified_identifier =
        Qualified_identifier.make
          ~location:(Identifier.location identifier)
          ~namespaces identifier
      in
      CallGraphState.set_program_display_name state cid qualified_identifier
  | Sgn.Recursive_declarations { declarations; _ } ->
      List1.iter (visit_sgn_declaration state namespaces) declarations
  | Sgn.Module { identifier; entries; _ } ->
      List.iter (visit_sgn_entry state (namespaces @ [ identifier ])) entries
  | Sgn.Typ _
  | Sgn.Const _
  | Sgn.CompTyp _
  | Sgn.CompCotyp _
  | Sgn.CompConst _
  | Sgn.CompDest _
  | Sgn.CompTypAbbrev _
  | Sgn.Schema _
  | Sgn.Val _ ->
      ()

let construct_call_graph_state : Sgn.sgn -> state =
 fun sgn ->
  let state = CallGraphState.create () in
  visit_sgn state sgn;
  state

(** {2 Printing Result} *)

let rec pp_call_graph_sgn : state -> Format.formatter -> Sgn.sgn -> unit =
 fun state ppf sgn -> List1.iter (pp_call_graph_sgn_file state ppf) sgn

and pp_call_graph_sgn_file :
    state -> Format.formatter -> Sgn.sgn_file -> unit =
 fun state ppf { Sgn.entries; _ } ->
  List.iter (pp_call_graph_sgn_entry state ppf) entries

and pp_call_graph_sgn_entry : state -> Format.formatter -> Sgn.entry -> unit
    =
 fun state ppf -> function
  | Sgn.Declaration { declaration; _ } ->
      pp_call_graph_sgn_declaration state ppf declaration
  | Sgn.Pragma _
  | Sgn.Comment _ ->
      ()

and pp_call_graph_sgn_declaration :
    state -> Format.formatter -> Sgn.decl -> unit =
 fun state ppf -> function
  | Sgn.Theorem { cid; _ } -> (
      let display_name =
        CallGraphState.lookup_program_display_name state cid
      in
      let dependencies =
        CallGraphState.compute_program_call_dependencies state cid
      in
      let dependency_names =
        List.sort Qualified_identifier.compare
          (Id.Prog.Set.fold
             (fun x xs ->
               CallGraphState.lookup_program_display_name state x :: xs)
             dependencies [])
      in
      match dependency_names with
      | [] ->
          Format.fprintf ppf
            "@[<h 0>Theorem %a (%a) has no call dependencies.@]@.@."
            Qualified_identifier.pp display_name Location.pp
            (Qualified_identifier.location display_name)
      | _ ->
          Format.fprintf ppf
            "@[<h 0>Transitive call dependencies of theorem %a (%a):@]@;\
             <1 2>@[<v 0>%a@]@.@." Qualified_identifier.pp display_name
            Location.pp
            (Qualified_identifier.location display_name)
            (List.pp ~pp_sep:Format.pp_print_cut (fun ppf x ->
                 Format.fprintf ppf "@[<h 0>- %a (%a)@]"
                   Qualified_identifier.pp x Location.pp
                   (Qualified_identifier.location x)))
            dependency_names)
  | Sgn.Recursive_declarations { declarations; _ } ->
      List1.iter (pp_call_graph_sgn_declaration state ppf) declarations
  | Sgn.Module { entries; _ } ->
      List.iter (pp_call_graph_sgn_entry state ppf) entries
  | Sgn.Typ _
  | Sgn.Const _
  | Sgn.CompTyp _
  | Sgn.CompCotyp _
  | Sgn.CompConst _
  | Sgn.CompDest _
  | Sgn.CompTypAbbrev _
  | Sgn.Schema _
  | Sgn.Val _ ->
      ()

(** {2 Dependency Data to JSON} *)

let json_of_location : Location.t -> Yojson.Safe.t =
 fun location ->
  if Location.is_ghost location then `Null
  else
    `Assoc
      [ ("filename", `String (Location.filename location))
      ; ("start_line", `Int (Location.start_line location))
      ; ("start_column", `Int (Location.start_column location))
      ; ("stop_line", `Int (Location.stop_line location))
      ; ("stop_column", `Int (Location.stop_column location))
      ]

let rec json_of_call_graph_sgn : state -> Sgn.sgn -> Yojson.Safe.t =
 fun state sgn ->
  `List
    (List.flatten
       (List1.to_list (List1.map (json_of_call_graph_sgn_file state) sgn)))

and json_of_call_graph_sgn_file : state -> Sgn.sgn_file -> Yojson.Safe.t list
    =
 fun state { Sgn.entries; _ } ->
  let programs =
    entries
    |> List.map (dependencies_to_json_call_graph_sgn_entry state)
    |> List.flatten
  in
  programs

and dependencies_to_json_call_graph_sgn_entry :
    state -> Sgn.entry -> Yojson.Safe.t list =
 fun state -> function
  | Sgn.Declaration { declaration; _ } ->
      json_of_call_graph_sgn_declaration state declaration
  | Sgn.Pragma _
  | Sgn.Comment _ ->
      []

and json_of_cid_prog : Id.cid_prog -> Yojson.Safe.t =
 fun cid -> `Int (Id.Prog.to_int cid)

and json_of_call_graph_sgn_declaration :
    state -> Sgn.decl -> Yojson.Safe.t list =
 fun state -> function
  | Sgn.Theorem { cid; _ } ->
      let display_name =
        cid |> CallGraphState.lookup_program_display_name state
      in
      let immediate_dependencies =
        cid
        |> CallGraphState.get_immediate_dependencies state
        |> Id.Prog.Set.to_seq |> Seq.map json_of_cid_prog |> List.of_seq
      in
      let dependencies =
        cid
        |> CallGraphState.compute_program_call_dependencies state
        |> Id.Prog.Set.to_seq |> Seq.map json_of_cid_prog |> List.of_seq
      in
      [ `Assoc
          [ ("id", json_of_cid_prog cid)
          ; ( "qualified_identifier"
            , `String (Qualified_identifier.show display_name) )
          ; ( "location"
            , json_of_location (Qualified_identifier.location display_name)
            )
          ; ("immediate_dependencies", `List immediate_dependencies)
          ; ("transitive_dependencies", `List dependencies)
          ]
      ]
  | Sgn.Recursive_declarations { declarations; _ } ->
      List1.to_list declarations
      |> List.map (json_of_call_graph_sgn_declaration state)
      |> List.flatten
  | Sgn.Module { entries; _ } ->
      entries
      |> List.map (dependencies_to_json_call_graph_sgn_entry state)
      |> List.flatten
  | Sgn.Typ _
  | Sgn.Const _
  | Sgn.CompTyp _
  | Sgn.CompCotyp _
  | Sgn.CompConst _
  | Sgn.CompDest _
  | Sgn.CompTypAbbrev _
  | Sgn.Schema _
  | Sgn.Val _ ->
      []

(** {2 Driver} *)

(** CLI usage: [dune exec beluga_call_graph ./path-to-signature.cfg] *)

let main () =
  let args = List.tl (Array.to_list Sys.argv) in
  (match args with
  | [ file ] ->
      let _, sgn = Load.load_fresh file in
      let call_graph = construct_call_graph_state sgn in
      Format.fprintf Format.std_formatter "%a@."
        (Yojson.Safe.pretty_print ~std:true)
        (json_of_call_graph_sgn call_graph sgn)
  | [] ->
      Format.fprintf Format.err_formatter
        "Provide the file path to the Beluga signature.@.";
      Stdlib.exit 2
  | _ ->
      Format.fprintf Format.err_formatter
        "Provide only one file path to the Beluga signature.@.";
      Stdlib.exit 2);
  Format.fprintf Format.std_formatter "%s@."
    (Beluga.Coverage.get_information ())

let () =
  try main () with
  | e ->
      Format.fprintf Format.err_formatter "%s@." (Printexc.to_string e);
      Stdlib.exit 1
