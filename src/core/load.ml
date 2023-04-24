(* Loading files *)

open Support
open Beluga_syntax
open Beluga_parser

let dprintf, _, _ = Debug.(makeFunctions' (toFlags [ 11 ]))

open Debug.Fmt

module type LOAD_STATE = sig
  include Imperative_state.IMPERATIVE_STATE

  val read_signature_file :
    state -> filename:String.t -> Synext.signature_file

  val reconstruct_signature_file :
    state -> Synext.signature_file -> Synint.Sgn.sgn

  val get_leftover_vars :
    state -> (Abstract.free_var Synint.LF.ctx * Location.t) List.t
end

module Make_load_state
    (Disambiguation_state : Beluga_parser.DISAMBIGUATION_STATE)
    (Disambiguation : Beluga_parser.DISAMBIGUATION
                        with type state = Disambiguation_state.state)
    (Signature_reconstruction_state : Recsgn_state
                                      .SIGNATURE_RECONSTRUCTION_STATE)
    (Signature_reconstruction : Recsgn.SIGNATURE_RECONSTRUCTION
                                  with type state =
                                    Signature_reconstruction_state.state) =
struct
  module Parser_state =
    Parser_combinator.Make_persistent_state (Located_token)
  module Parser = Beluga_parser.Make (Parser_state) (Disambiguation_state)

  type state =
    { disambiguation_state : Disambiguation_state.state
    ; signature_reconstruction_state : Signature_reconstruction_state.state
    }

  let create_state disambiguation_state signature_reconstruction_state =
    { disambiguation_state; signature_reconstruction_state }

  include (
    Imperative_state.Make (struct
      type nonrec state = state
    end) :
      Imperative_state.IMPERATIVE_STATE with type state := state)

  let read_signature_file state ~filename =
    let signature_file =
      In_channel.with_open_bin filename (fun in_channel ->
          let initial_location = Location.initial filename in
          let token_sequence =
            Lexer.lex_input_channel ~initial_location in_channel
          in
          let parsing_state =
            Parser_state.initial ~initial_location token_sequence
          in
          let _parsing_state', signature_file =
            Parser.Parsing.run_exn
              Parser.Parsing.(only signature_file)
              parsing_state
          in
          signature_file)
    in
    Disambiguation.disambiguate_signature_file state.disambiguation_state
      signature_file

  let reconstruct_signature_file state signature =
    Signature_reconstruction.reconstruct_signature_file
      state.signature_reconstruction_state signature

  let get_leftover_vars state =
    Signature_reconstruction_state.get_leftover_vars
      state.signature_reconstruction_state
end

module type LOAD = sig
  include Imperative_state.IMPERATIVE_STATE

  val load : state -> String.t -> String.t List.t * Synint.Sgn.sgn
end

let read_signature_and_write_html filename =
  let source_files =
    List.map Pair.snd (Config_parser.read_configuration ~filename)
  in
  let directory = Sys.getcwd () in
  let signature =
    Parser.read_multi_file_signature (List1.unsafe_of_list source_files)
  in
  Beluga_html.pp_signature_to_files ~directory signature;
  let opam_switch_prefix = Sys.getenv "OPAM_SWITCH_PREFIX" in
  let css_filename =
    Filename.concat opam_switch_prefix
      (Filename.concat "share" (Filename.concat "beluga" "beluga.css"))
  in
  Files.copy_file ~source:css_filename
    ~destination:
      (Filename.concat
         (Filename.dirname filename)
         (Filename.basename css_filename))

module Make_load (Load_state : LOAD_STATE) = struct
  include Load_state

  let forbid_leftover_vars path = function
    | Option.None -> ()
    | Option.Some vars ->
        Chatter.print 1 (fun ppf ->
            Format.fprintf ppf
              "@[<v>## Leftover variables: %s  ##@,  @[%a@]@]@\n" path
              Recsgn.fmt_ppr_leftover_vars vars);
        Error.raise (Abstract.Error (Location.ghost, Abstract.LeftoverVars))

  let load_file state filename =
    let sgn = read_signature_file state ~filename in

    Chatter.print 1 (fun ppf ->
        Format.fprintf ppf "## Type Reconstruction begin: %s ##@\n" filename);

    let sgn' = reconstruct_signature_file state sgn in
    let leftoverVars = get_leftover_vars state in

    Chatter.print 2 (fun ppf ->
        Format.fprintf ppf
          "@[<v>## Internal syntax dump: %s ##@,@[<v>%a@]@]@\n" filename
          Pretty.Int.DefaultPrinter.fmt_ppr_sgn sgn');

    Chatter.print 1 (fun ppf ->
        Format.fprintf ppf "## Type Reconstruction done:  %s ##@\n" filename);

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
          Format.fprintf ppf "## Coverage checking done: %s  ##@\n" filename);

    Logic.runLogic ();
    (if Bool.not (Holes.none ()) then
       let open Format in
       Chatter.print 1 (fun ppf ->
           Format.fprintf ppf "@[<v>## Holes: %s  ##@,@[<v>%a@]@]@\n"
             filename
             (pp_print_list Interactive.fmt_ppr_hole)
             (Holes.list ())));

    forbid_leftover_vars filename
      (Option.from_predicate List.nonempty leftoverVars);

    if !Typeinfo.generate_annotations then Typeinfo.print_annot filename;
    if !Monitor.on || !Monitor.onf then Monitor.print_timers ();

    sgn'

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
    let signature' = List.concat (traverse_list state load_one all_paths) in

    if !Options.Html.enabled then
      read_signature_and_write_html configuration_filename;

    (all_paths, signature')
end

module Load_state =
  Make_load_state (Parser.Disambiguation_state) (Parser.Disambiguation)
    (Recsgn_state.Signature_reconstruction_state)
    (Recsgn.Signature_reconstruction)
module Load = Make_load (Load_state)

let load disambiguation_state signature_reconstruction_state filename =
  let state =
    Load_state.create_state disambiguation_state
      signature_reconstruction_state
  in
  Load.load state filename

let load_fresh filename =
  let disambiguation_state =
    Parser.Disambiguation_state.create_initial_state ()
  in
  let indexing_state = Index_state.Indexing_state.create_initial_state () in
  let signature_reconstruction_state =
    Recsgn_state.Signature_reconstruction_state.create_initial_state
      indexing_state
  in
  load disambiguation_state signature_reconstruction_state filename
