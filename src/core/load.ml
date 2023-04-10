(* Loading files *)

open Support
open Beluga_syntax
open Beluga_parser

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [ 11 ]))

open Debug.Fmt

module type LOAD_STATE = sig
  type state

  val read_signature_file :
    state -> filename:String.t -> Synext.signature_file

  val reconstruct_signature_file :
    state -> Synext.signature_file -> Synint.Sgn.sgn

  val get_leftover_vars :
    state -> (Abstract.free_var Synint.LF.ctx * Location.t) List.t

  val traverse_list_void :
    state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t
end

module Load_state = struct
  module Beluga_parser = Beluga_parser.Mutable
  module Parsing = Beluga_parser.Parsing
  module Disambiguation = Beluga_parser.Disambiguation
  module Disambiguation_state = Beluga_parser.Disambiguation_state
  module Index_state = Index_state_demonad.Mutable_indexing_state
  module Signature_reconstruction_state =
    Recsgn_state_demonad.Signature_reconstruction_state
  module Signature_reconstruction = Recsgn_demonad.Signature_reconstruction

  type state =
    { disambiguation_state : Disambiguation_state.state
    ; signature_reconstruction_state : Signature_reconstruction_state.state
    }

  let create_initial_state () =
    { disambiguation_state = Disambiguation_state.create_initial_state ()
    ; signature_reconstruction_state =
        Signature_reconstruction_state.initial_state
          (Index_state.create_initial_state ())
    }

  let read_signature_file state ~filename =
    In_channel.with_open_bin filename (fun in_channel ->
        let initial_location = Location.initial filename in
        let initial_parser_state =
          Beluga_parser.make_initial_state_from_channel ~initial_location
            ~disambiguation_state:state.disambiguation_state
            ~channel:in_channel
        in
        Beluga_parser.eval
          (Beluga_parser.parse_and_disambiguate
             ~parser:Parsing.(only signature_file)
             ~disambiguator:Disambiguation.disambiguate_signature_file)
          initial_parser_state)

  let reconstruct_signature_file state signature =
    Signature_reconstruction.reconstruct_signature_file
      state.signature_reconstruction_state signature

  let get_leftover_vars state =
    Signature_reconstruction_state.get_leftover_vars
      state.signature_reconstruction_state

  let rec traverse_list_void state f l =
    match l with
    | [] -> ()
    | x :: xs ->
        f state x;
        traverse_list_void state f xs
end

module Make_load (Load_state : LOAD_STATE) = struct
  include Load_state

  let forbid_leftover_vars path = function
    | Option.None -> ()
    | Option.Some vars ->
        Chatter.print 1 (fun ppf ->
            Format.fprintf ppf
              "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@." path
              Recsgn.fmt_ppr_leftover_vars vars);
        Error.raise (Abstract.Error (Location.ghost, Abstract.LeftoverVars))

  let load_file state filename =
    let sgn = read_signature_file state ~filename in

    Chatter.print 1 (fun ppf ->
        Format.fprintf ppf "## Type Reconstruction begin: %s ##@." filename);

    let sgn' = reconstruct_signature_file state sgn in
    let leftoverVars = get_leftover_vars state in

    Chatter.print 2 (fun ppf ->
        Format.fprintf ppf
          "@[<v>## Internal syntax dump: %s ##@,@[<v>%a@]@]@." filename
          Pretty.Int.DefaultPrinter.fmt_ppr_sgn sgn');

    Chatter.print 1 (fun ppf ->
        Format.fprintf ppf "## Type Reconstruction done:  %s ##@." filename);

    Coverage.iter (function
      | Coverage.Success -> ()
      | Coverage.Failure message ->
          if !Coverage.warningOnly then
            Coverage.add_information
              (Format.asprintf "WARNING: Cases didn't cover: %s" message)
          else
            raise (Coverage.Error (Location.ghost, Coverage.NoCover message)));

    if !Coverage.enableCoverage then
      Chatter.print 2 (fun ppf ->
          Format.fprintf ppf "## Coverage checking done: %s  ##@." filename);

    Logic.runLogic ();
    (if Bool.not (Holes.none ()) then
       let open Format in
       Chatter.print 1 (fun ppf ->
           Format.fprintf ppf "@[<v>## Holes: %s  ##@,@[<v>%a@]@]@." filename
             (pp_print_list Interactive.fmt_ppr_hole)
             (Holes.list ())));

    forbid_leftover_vars filename
      (Option.from_predicate List.nonempty leftoverVars);

    if !Typeinfo.generate_annotations then Typeinfo.print_annot filename;
    if !Monitor.on || !Monitor.onf then Monitor.print_timers ()

  let load_one state path =
    try load_file state path with
    | e ->
        dprintf (fun p ->
            p.fmt "@[<v 2>[load_one] %s backtrace:@,@[%a@]@]" path
              Format.pp_print_string
              (Printexc.get_backtrace ()));
        Error.raise e

  let load state configuration_filename =
    let all_paths =
      List.map Pair.snd
        (Config_parser.read_configuration ~filename:configuration_filename)
    in
    dprintf (fun p ->
        p.fmt "[load] @[<v>full load@,resolved %s =@,  @[<hv>%a@]@]"
          configuration_filename
          (Format.pp_print_list ~pp_sep:Format.comma (fun ppf x ->
               Format.fprintf ppf "%s" x))
          all_paths);
    Gensym.reset ();
    Store.clear ();
    Typeinfo.clear_all ();
    Holes.clear ();
    traverse_list_void state load_one all_paths;
    all_paths
end

include Make_load (Load_state)

let load filename =
  let state = Load_state.create_initial_state () in
  load state filename
