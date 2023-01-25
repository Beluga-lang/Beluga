open Support
open Debug.Fmt

let raise = raise

exception Violation of string

let violation msg =
  Debug.printf (fun p -> p.fmt "[violation] %s" msg);
  raise (Violation msg)

(** The exception variant for exceptions annotated with source code locations
    for reporting. This exception variant must not be made public. *)
exception
  Located_exception of
    { cause : exn
    ; locations : Location.t List1.t
    }

let[@inline] located_exception locations cause =
  Located_exception { cause; locations }

let[@inline] located_exception1 location cause =
  located_exception (List1.singleton location) cause

let[@inline] located_exception2 location1 location2 cause =
  located_exception (List1.from location1 [ location2 ]) cause

let[@inline] raise_at locations cause =
  raise (located_exception locations cause)

let[@inline] raise_at1 location cause =
  raise (located_exception1 location cause)

let[@inline] raise_at2 location1 location2 cause =
  raise (located_exception2 location1 location2 cause)

let[@inline] discard_locations exn =
  match exn with
  | Located_exception { cause; _ } -> cause
  | exn -> exn

let[@inline] locations exn =
  match exn with
  | Located_exception { locations; _ } -> Option.some locations
  | _ -> Option.none

(** The exception variant for the composition of multiple related exceptions.
    This exception variant must not be made public. *)
exception Composite_exception of { causes : exn List2.t }

let[@inline] composite_exception causes = Composite_exception { causes }

let[@inline] composite_exception2 cause1 cause2 =
  composite_exception (List2.from cause1 cause2 [])

(** The exception variant for the aggregation of multiple unrelated
    exceptions. This exception variant must not be made public. *)
exception Aggregate_exception of { exceptions : exn List2.t }

let[@inline] aggregate_exception exceptions =
  Aggregate_exception { exceptions }

let[@inline] aggregate_exception2 exception1 exception2 =
  aggregate_exception (List2.pair exception1 exception2)

(** The exception variant used in {!raise_not_implemented} to signal that a
    case in the code is currently not implemented, but should be implemented
    someday. This exception variant must not be made public. *)
exception Not_implemented of string

let raise_not_implemented ?location msg =
  match location with
  | Option.None -> raise (Not_implemented msg)
  | Option.Some location -> raise_at1 location (Not_implemented msg)

type print_result = string

let error_format_buffer = Buffer.create 1024

let error_format = Format.formatter_of_buffer error_format_buffer

let register_printer f =
  Printexc.register_printer (fun e ->
      try Option.some (f e) with
      | Match_failure _ -> Option.none)

let register_printer' f = Printexc.register_printer f

let print f =
  (* Print to stderr any uncaught exception resulting from applying f to
     error_format. Such an exception would be thrown when in the middle of
     printing an exception! *)
  Printexc.print f error_format;
  Format.pp_print_newline error_format ();
  Format.pp_print_flush error_format ();
  let str = Buffer.contents error_format_buffer in
  Buffer.reset error_format_buffer;
  str

let register_printing_function (extract : exn -> 'a option)
    (fmt_ppr : Format.formatter -> 'a -> unit) : unit =
  let open Fun in
  register_printer'
    (Option.map (fun e -> print (fun ppf -> fmt_ppr ppf e)) ++ extract)

let register_located_printing_function
    (extract : exn -> (Location.t * 'a) option)
    (fmt_ppr : Format.formatter -> 'a -> unit) : unit =
  let f (loc, e) =
    print (fun ppf ->
        Format.fprintf ppf "@[<v>%a:@,%a@]" Location.print loc fmt_ppr e)
  in
  let open Fun in
  register_printer' (Option.map f ++ extract)

let print_location loc =
  Format.fprintf error_format "%a:@," Location.print loc

let print_with_location loc f =
  print_location loc;
  print f

(* Since this printer is registered first, it will be executed only if all
   other printers fail. *)
let () =
  Printexc.register_printer (fun cause ->
      Option.some
        (Format.asprintf
           "Uncaught exception.@ Please report this as a bug.@.%s"
           (Printexc.to_string_default cause)))

let report_mismatch ppf title title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2
    =
  Format.fprintf ppf "@[<v>%s@," title;
  Format.fprintf ppf "    @[<v>%s:@,  %a@,%s:@,  %a@]@,@]" title_obj1 pp_obj1
    obj1 title_obj2 pp_obj2 obj2

(* The following is for coverage. Probably needs to be phased out. *)
let information = ref []

let reset_information () = information := []

let get_information () =
  Format.stringify
    (List.pp ~pp_sep:Format.pp_print_newline Format.pp_print_string)
    (List.rev !information)

let add_information message = information := message :: !information

(** Register some basic printers. *)
let () =
  register_printer (fun [@warning "-8"] (Sys_error msg) ->
      print (fun ppf -> Format.fprintf ppf "System error: %s" msg));

  register_printer (fun [@warning "-8"] (Violation msg) ->
      print (fun ppf ->
          Format.fprintf ppf
            "@[<v>Internal error (please report as a bug):@,@[%a@]@]"
            Format.pp_print_string msg))

(** {1 Printing Located Exceptions} *)

(** [tokenize_line lexer_buffer] tokenizes from [lexer_buffer] a line ending
    in the character ['\n'], without including it in the line. The newline
    character is skipped for subsequent tokenizations. The length of the line
    as determined by the lexer is included to properly handle UTF-8-encoded
    lines in error-reporting.

    For instance, if the buffer contains ["This is a line.\n"], then the
    tokenized line is ["This is a line."] with length [15]. *)
let tokenize_line lexer_buffer =
  match%sedlex lexer_buffer with
  | eof -> Option.none
  | Star (Compl '\n') ->
      let line = Sedlexing.Utf8.lexeme lexer_buffer in
      let length = Sedlexing.lexeme_length lexer_buffer in
      (* Skip the next newline character, if any. *)
      ignore (Sedlexing.next lexer_buffer : Uchar.t Option.t);
      Option.some (length, line)
  | _ -> assert false

exception Failed_to_read_line of Int.t

(** [read_lines line_numbers lexer_buffer] reads from [lexer_buffer] the
    lines having corresponding lines [line_numbers]. It is assumed that
    [line_numbers] is sorted in ascending order, without duplicates so that
    lines can be read sequentially. *)
let rec read_lines line_numbers lexer_buffer =
  match line_numbers with
  | [] -> []
  | line_number :: line_numbers' ->
      let rec read_line line_number =
        match tokenize_line lexer_buffer with
        | Option.None -> raise (Failed_to_read_line line_number)
        | Option.Some line_string ->
            let start, _stop = Sedlexing.lexing_positions lexer_buffer in
            if start.Lexing.pos_lnum = line_number then line_string
            else read_line line_number
      in
      let line = read_line line_number in
      let lines = read_lines line_numbers' lexer_buffer in
      line :: lines

(** [location_line_numbers location] is the set of line numbers of characters
    in the range of [location]. *)
let location_line_numbers location =
  let start_line = Location.start_line location in
  let stop_line = Location.stop_line location in
  let rec build_line_number_set current_line acc =
    if current_line <= stop_line then
      build_line_number_set (current_line + 1) (Int.Set.add current_line acc)
    else acc
  in
  build_line_number_set start_line Int.Set.empty

(** [group_locations_by_filename locations] is the map from filenames to
    locations in [locations]. Ghost locations in [locations] are ignored. *)
let group_locations_by_filename =
  let rec group_locations_by_filename locations acc =
    match locations with
    | [] -> acc
    | location :: locations' -> (
        if Location.is_ghost location then
          (* Skip ghost locations as they do not have filenames *)
          group_locations_by_filename locations' acc
        else
          let filename = Location.filename location in
          match String.Map.find_opt filename acc with
          | Option.None ->
              group_locations_by_filename locations'
                (String.Map.add filename [ location ] acc)
          | Option.Some locations ->
              group_locations_by_filename locations'
                (String.Map.add filename (location :: locations) acc))
  in
  fun locations -> group_locations_by_filename locations String.Map.empty

let collect_location_line_numbers_by_filename locations_by_filename =
  String.Map.map
    (fun locations ->
      List.fold_left
        (fun acc location ->
          Int.Set.union acc (location_line_numbers location))
        Int.Set.empty locations)
    locations_by_filename

let read_file_lines line_numbers_by_filename =
  String.Map.mapi
    (fun filename line_numbers_set ->
      let line_numbers_list = Int.Set.elements line_numbers_set in
      Files.with_open_bin filename (fun in_channel ->
          let lexer_buffer = Sedlexing.Utf8.from_channel in_channel in
          let lines = read_lines line_numbers_list lexer_buffer in
          List.combine line_numbers_list lines))
    line_numbers_by_filename

(** [make_caret_line start_column stop_column length] makes a string of
    spaces and carets of codepoint length [length], with carets in code point
    range [start_column] inclusively to [stop_column] exclusively.

    Be wary that columns start at [1], whereas string indexes start at [0].

    For instance, [make_caret_line 12 16 17] produces ["           ^^^^^ "],
    which is suitable for underlining ["error"] in ["This is an error."]. *)
let[@inline] make_caret_line ~start_column ~stop_column length =
  let caret_start_index = start_column - 1 in
  let caret_stop_index = stop_column - 1 in
  String.init length (fun i ->
      if caret_start_index <= i && i < caret_stop_index then '^' else ' ')

(** [make_location_snippet location lines_by_number] is a list of pairs of
    strings [(l1, u1); (l2, u2); ...; (ln, un)] where [li] is an input source
    line in [lines_by_number] and [ui] is a line of carets ['^'] underlining
    codepoints in [location].

    That is, with [location] spanning from some start line to some stop line,
    and prefetched lines [lines_by_number] indexed by their line number, this
    function selects the lines that include [location], and generates lines
    of caret underlining codepoints in [location]. *)
let make_location_snippet location lines_by_number =
  let start_line = Location.start_line location in
  let start_column = Location.start_column location in
  let stop_line = Location.stop_line location in
  let stop_column = Location.stop_column location in
  match
    (* Get the lines spanned by [location] in [lines_by_number]. *)
    List.filter_map
      (fun (line_number, line) ->
        if start_line <= line_number && line_number <= stop_line then
          Option.some line
        else Option.none)
      lines_by_number
  with
  | [] ->
      assert false
      (* [lines_by_number] is assumed to contain at least a line spanned by
         [location]. *)
  | [ (length, x) ] ->
      (* The location spans one line, so the caret start and stop columns
         occur in the same line. *)
      let underline = make_caret_line ~start_column ~stop_column length in
      [ (x, underline) ]
  | (length_first, x_first) :: xs ->
      (* The location spans at least two lines. In the first line, the caret
         start column is [start_column], and in the last line, the caret stop
         column is [stop_column]. All other lines are fully underlined. *)
      let underline_first =
        make_caret_line ~start_column ~stop_column:(length_first + 1)
          length_first
      in
      let rec make_rest = function
        | [] ->
            assert false (* [add_rest] is never called with an empty list. *)
        | [ (length_last, x_last) ] ->
            let underline_last =
              make_caret_line ~start_column:1 ~stop_column length_last
            in
            [ (x_last, underline_last) ]
        | (length_intermediate, x_intermediate) :: xs ->
            let underline_intermediate =
              make_caret_line ~start_column:1
                ~stop_column:(length_intermediate + 1) length_intermediate
            in
            (x_intermediate, underline_intermediate) :: make_rest xs
      in
      (x_first, underline_first) :: make_rest xs

let make_location_snippets locations =
  (* Group locations by filename *)
  let grouped = group_locations_by_filename locations in
  (* For each file, order the locations by the start position *)
  let sorted_groups =
    String.Map.map (List.sort Location.compare_start) grouped
  in
  (* Read the lines corresponding to the locations in [sorted_groups], mapped
     by filename *)
  let grouped_lines =
    read_file_lines (collect_location_line_numbers_by_filename sorted_groups)
  in
  (* For each file, for each location, construct the corresponding location
     snippet using the read lines [grouped_lines] *)
  sorted_groups |> String.Map.to_seq
  |> Seq.flat_map (fun (filename, locations) ->
         let lines = String.Map.find filename grouped_lines in
         locations |> List.to_seq
         |> Seq.map (fun location ->
                let snippet = make_location_snippet location lines in
                (location, snippet)))
  |> Seq.to_list

let located_exception_to_string cause locations =
  try
    let snippets = make_location_snippets locations in
    (* See ANSI escape sequences for the meaning of ["\x1b[1m"],
       ["\x1b[31m"], ["\x1b[1;31m"] and ["\x1b[0m"] for changing the font
       style and color of terminal outputs. *)
    let pp_snippet ppf (location, lines) =
      Format.fprintf ppf "@[<v 0>\x1b[1m%a:\x1b[0m@,%a@]" Location.pp
        location
        (List.pp ~pp_sep:Format.pp_print_cut (fun ppf (line, carets) ->
             Format.fprintf ppf "%s@,\x1b[31m%s\x1b[0m" line carets))
        lines
    in
    Format.asprintf "@[<v 0>%a@,\x1b[1;31mError:\x1b[0m %s@]"
      (List.pp ~pp_sep:Format.pp_print_cut pp_snippet)
      snippets
      (Printexc.to_string cause)
  with
  | _ ->
      (* An exception occurred while trying to read the snippets. Report the
         exception without the snippets. *)
      Format.asprintf "@[<v 0>%a@,%s@]"
        (List.pp ~pp_sep:Format.pp_print_cut Location.pp)
        locations
        (Printexc.to_string cause)

(** The exception raised when a pretty-printing function for exceptions
    encounters an unsupported exception variant. This exception variant must
    not be made public, and should only be used in
    {!raise_unsupported_exception_printing} and
    {!register_exception_printer}. *)
exception Unsupported_exception_printing of exn

let raise_unsupported_exception_printing exn =
  raise (Unsupported_exception_printing exn)

let register_exception_printer ppf =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify ppf exn) with
      | Unsupported_exception_printing _ -> Option.none)

let () =
  Printexc.register_printer (function
    | Located_exception { cause; locations } ->
        Option.some
          (located_exception_to_string cause (List1.to_list locations))
    | Composite_exception { causes } ->
        Option.some
          (Format.asprintf "@[<v 0>%a@]"
             (List2.pp ~pp_sep:Format.pp_print_cut String.pp)
             (List2.map Printexc.to_string causes))
    | Aggregate_exception { exceptions } ->
        Option.some
          (Format.asprintf "@[<v 0>%a@]"
             (List2.pp
                ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,@,")
                String.pp)
             (List2.map Printexc.to_string exceptions))
    | _ -> Option.none)

let () =
  register_exception_printer (fun ppf -> function
    | Not_implemented msg ->
        Format.fprintf ppf "@[<v 0>Not implemented.@,%s@]" msg
    | exn -> raise_unsupported_exception_printing exn)
