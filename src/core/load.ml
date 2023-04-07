(* Loading files *)

open Support
open Beluga_syntax
open Beluga_parser

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [ 11 ]))

open Debug.Fmt

module type LOAD_STATE = sig
  include State.STATE

  val read_signature_file : filename:String.t -> Synext.signature_file t

  val reconstruct_signature_file : Synext.signature_file -> Synint.Sgn.sgn t

  val get_leftover_vars :
    (Abstract.free_var Synint.LF.ctx * Location.t) List.t t
end

module Load_state = struct
  module Beluga_parser = Beluga_parser.Mutable
  module Parsing = Beluga_parser.Parsing
  module Disambiguation = Beluga_parser.Disambiguation
  module Disambiguation_state = Beluga_parser.Disambiguation_state
  module Index_state = Index_state.Persistent_indexing_state
  module Signature_reconstruction_state =
    Recsgn_state.Signature_reconstruction_state

  type state =
    { disambiguation_state : Disambiguation_state.state
    ; signature_reconstruction_state : Signature_reconstruction_state.state
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let initial_state =
    { disambiguation_state = Disambiguation_state.create_initial_state ()
    ; signature_reconstruction_state =
        Signature_reconstruction_state.initial_state
          Index_state.initial_state
    }

  let read_signature_file ~filename =
    let* { disambiguation_state; _ } = get in
    In_channel.with_open_bin filename (fun in_channel ->
        let initial_location = Location.initial filename in
        let initial_parser_state =
          Beluga_parser.make_initial_state_from_channel ~initial_location
            ~disambiguation_state ~channel:in_channel
        in
        let s, x =
          Beluga_parser.run
            (Beluga_parser.parse_and_disambiguate
               ~parser:Parsing.(only signature_file)
               ~disambiguator:Disambiguation.disambiguate_signature_file)
            initial_parser_state
        in
        let _, disambiguation_state' =
          Beluga_parser.get_disambiguation_state s
        in
        let* () =
          modify (fun state ->
              { state with disambiguation_state = disambiguation_state' })
        in
        return x)

  let reconstruct_signature_file signature =
    let* { signature_reconstruction_state; _ } = get in
    let signature_reconstruction_state', signature' =
      Signature_reconstruction_state.run
        (Recsgn.Signature_reconstruction.reconstruct_signature_file signature)
        signature_reconstruction_state
    in
    let* () =
      modify (fun state ->
          { state with
            signature_reconstruction_state = signature_reconstruction_state'
          })
    in
    return signature'

  let get_leftover_vars =
    let* { signature_reconstruction_state; _ } = get in
    let _, leftover_vars =
      Signature_reconstruction_state.get_leftover_vars
        signature_reconstruction_state
    in
    return leftover_vars
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

  let load_file filename =
    let* sgn = read_signature_file ~filename in

    Chatter.print 1 (fun ppf ->
        Format.fprintf ppf "## Type Reconstruction begin: %s ##@." filename);

    let* sgn' = reconstruct_signature_file sgn in
    let* leftoverVars = get_leftover_vars in

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
    if !Monitor.on || !Monitor.onf then Monitor.print_timers ();

    return ()

  let load_one path =
    try_catch
      (lazy (load_file path))
      ~on_exn:(fun e ->
        dprintf (fun p ->
            p.fmt "@[<v 2>[load_one] %s backtrace:@,@[%a@]@]" path
              Format.pp_print_string
              (Printexc.get_backtrace ()));
        Error.raise e)

  let load configuration_filename =
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
    let* () = traverse_list_void load_one all_paths in
    return all_paths
end

include Make_load (Load_state)

let load filename = eval (load filename) Load_state.initial_state
