open Support
open Debug.Fmt

let raise = raise

let printers : (exn -> Format.formatter -> unit) list Atomic.t =
  Atomic.make []

let rec register_exception_printer printer =
  (* This implementation is adapted from {!Printexc.register_printer}. *)
  let old_printers = Atomic.get printers in
  let new_printers = printer :: old_printers in
  let success = Atomic.compare_and_set printers old_printers new_printers in
  if Bool.not success then
    (* A concurrent write occurred on {!printers}. Retry registering the
       exception printer. *) register_exception_printer printer

(** The exception raised when a pretty-printing function for exceptions
    encounters an unsupported exception variant. This exception variant must
    not be made public, and should only be used in
    {!raise_unsupported_exception_printing} and
    {!register_exception_printer}. *)
exception Unsupported_exception_printing of exn

let raise_unsupported_exception_printing exn =
  raise (Unsupported_exception_printing exn)

let find_printer_opt exn =
  let printers = Atomic.get printers in
  List.find_map
    (fun printer ->
      try Option.some (printer exn) with
      | Unsupported_exception_printing _ -> Option.none)
    printers

let find_printer exn =
  match find_printer_opt exn with
  | Option.Some printer -> printer
  | Option.None -> raise_unsupported_exception_printing exn

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

let[@inline] raise_at1_opt location_opt cause =
  match location_opt with
  | Option.None -> raise cause
  | Option.Some location -> raise_at1 location cause

(** The exception variant for the composition of multiple related exceptions.
    This exception variant must not be made public. *)
exception Composite_exception of { causes : exn List2.t }

let[@inline] composite_exception causes = Composite_exception { causes }

let[@inline] composite_exception2 cause1 cause2 =
  composite_exception (List2.from cause1 cause2 [])

let[@inline] raise_composite_exception causes =
  raise (composite_exception causes)

let[@inline] raise_composite_exception2 cause1 cause2 =
  raise (composite_exception2 cause1 cause2)

(** The exception variant for the aggregation of multiple unrelated
    exceptions. This exception variant must not be made public. *)
exception Aggregate_exception of { exceptions : exn List2.t }

let[@inline] aggregate_exception exceptions =
  Aggregate_exception { exceptions }

let[@inline] aggregate_exception2 exception1 exception2 =
  aggregate_exception (List2.pair exception1 exception2)

let[@inline] raise_aggregate_exception exceptions =
  raise (aggregate_exception exceptions)

let[@inline] raise_aggregate_exception2 exception1 exception2 =
  raise (aggregate_exception2 exception1 exception2)

(** The exception variant used in {!raise_not_implemented} to signal that a
    case in the code is currently not implemented, but should be implemented
    someday. This exception variant must not be made public. *)
exception Not_implemented of string

let raise_not_implemented ?location msg =
  match location with
  | Option.None -> raise (Not_implemented msg)
  | Option.Some location -> raise_at1 location (Not_implemented msg)

exception Violation of string

let raise_violation ?location msg =
  Debug.printf (fun p -> p.fmt "[violation] %s" msg);
  match location with
  | Option.None -> raise (Violation msg)
  | Option.Some location -> raise_at1 location (Violation msg)

let mismatch_reporter title title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2 =
  Format.dprintf "@[<v>%s@,    @[<v>%s:@,  %a@,%s:@,  %a@]@,@]" title
    title_obj1 pp_obj1 obj1 title_obj2 pp_obj2 obj2

(** {1 Printing Located Exceptions} *)

(** [replace_tabs_with_spaces line] is [line] where each tab character ['\t']
    is replaced with a single space [' '].

    In the lexer, each tab counts as one codepoint, so locations assume that
    each tab has length [1]. However, when we print source lines, tabs may be
    displayed with different lengths in the terminal depending on its
    configuration.

    This function is used to enforce that tabs are printed with length [1],
    which in turn makes it easier to print caret lines with the correct
    alignment. While we could pad the caret line with tabs on the left to
    somewhat fix the alignment of the carets, this would not fix the issue in
    the case where the range of characters to underline with carets contains
    a tab. *)
let replace_tabs_with_spaces line =
  String.concat " " (String.split_on_char '\t' line)

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
      Option.some (length, replace_tabs_with_spaces line)
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
      In_channel.with_open_bin filename (fun in_channel ->
          let lexer_buffer = Sedlexing.Utf8.from_channel in_channel in
          let lines = read_lines line_numbers_list lexer_buffer in
          List.combine line_numbers_list lines))
    line_numbers_by_filename

(** [split_utf8_line s pos] is [(left, right)] where [left] is the substring
    of [s] from the codepoint [0] to the codepoint [pos] exclusively, and
    [right] is the substring of [s] from the codepoint [pos] to the end of
    [s] inclusively.

    Note that [s] is a UTF-8-encoded string, so {!String.length} cannot be
    used to compute the distance between codepoints in [s]. *)
let split_utf8_line s pos =
  let lexer_buffer = Sedlexing.Utf8.from_string s in
  match%sedlex lexer_buffer with
  | Star any ->
      let length = Sedlexing.lexeme_length lexer_buffer in
      if pos <= 0 then ("", Sedlexing.Utf8.lexeme lexer_buffer)
      else if pos >= length then (Sedlexing.Utf8.lexeme lexer_buffer, "")
      else
        let left = Sedlexing.Utf8.sub_lexeme lexer_buffer 0 pos in
        let right = Sedlexing.Utf8.sub_lexeme lexer_buffer pos length in
        (left, right)
  | _ -> assert false

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

(** [line_number_prefix line_number max_line_count_length] is a prefix like
    [123 |] for [line_number = 123] for displaying source file numbers in
    error-reporting for located exceptions. [max_line_count_length] is the
    character length of the maximum line number that will be printed in the
    location snippet. This is used to add a left margin to the number to
    show. *)
let line_number_prefix line_number max_line_count_length =
  let line_number_string = Int.show line_number in
  let left_margin =
    max_line_count_length - String.length line_number_string
  in
  String.init left_margin (Fun.const ' ') ^ line_number_string ^ " |"

let add_line_number_prefix line_number max_line_count_length line carets =
  let prefix = line_number_prefix line_number max_line_count_length in
  let line' = prefix ^ line in
  let carets_left_margin =
    String.init (String.length prefix) (Fun.const ' ')
  in
  let carets' = carets_left_margin ^ carets in
  (line', carets')

(** [make_location_snippet location lines_by_number] is a list of pairs of
    strings [(l1, u1); (l2, u2); ...; (ln, un)] where [li] is an input source
    line in [lines_by_number] and [ui] is a line of carets ['^'] underlining
    codepoints in [location].

    That is, with [location] spanning from some start line to some stop line,
    and prefetched lines [lines_by_number] indexed by their line number and
    line length in codepoints, this function selects the lines that include
    [location], and generates lines of caret underlining codepoints in
    [location]. *)
let make_location_snippet location lines_by_number =
  let start_line = Location.start_line location in
  let start_column = Location.start_column location in
  let stop_line = Location.stop_line location in
  let stop_column = Location.stop_column location in
  let stop_line_count_length = String.length (Int.show stop_line) in
  match
    (* Get the lines spanned by [location] in [lines_by_number]. *)
    List.filter_map
      (fun (line_number, line) ->
        if start_line <= line_number && line_number <= stop_line then
          Option.some (line_number, line)
        else Option.none)
      lines_by_number
  with
  | [] ->
      assert false
      (* [lines_by_number] is assumed to contain at least a line spanned by
         [location]. *)
  | [ (n, (length, x)) ] ->
      (* The location spans one line, so the caret start and stop columns
         occur in the same line. *)
      if Location.spanned_offsets location <> 0 then
        (* Carets can be added directly under the line. *)
        let underline = make_caret_line ~start_column ~stop_column length in
        [ add_line_number_prefix n stop_line_count_length x underline ]
      else
        (* The location points to the space between two characters, i.e.
           [start_column = stop_column]. A space needs to be spliced in the
           input string so that it can be pointed to with a caret. *)
        let left, right = split_utf8_line x start_column in
        let underline =
          make_caret_line ~start_column ~stop_column:(stop_column + 1)
            (length + 1)
        in
        let spliced_line = Format.asprintf "%s %s" left right in
        [ add_line_number_prefix n stop_line_count_length spliced_line
            underline
        ]
  | (n_first, (length_first, x_first)) :: xs ->
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
        | [ (n_last, (length_last, x_last)) ] ->
            let underline_last =
              make_caret_line ~start_column:1 ~stop_column length_last
            in
            [ add_line_number_prefix n_last stop_line_count_length x_last
                underline_last
            ]
        | (n_intermediate, (length_intermediate, x_intermediate)) :: xs ->
            let underline_intermediate =
              make_caret_line ~start_column:1
                ~stop_column:(length_intermediate + 1) length_intermediate
            in
            add_line_number_prefix n_intermediate stop_line_count_length
              x_intermediate underline_intermediate
            :: make_rest xs
      in
      add_line_number_prefix n_first stop_line_count_length x_first
        underline_first
      :: make_rest xs

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

(* See ANSI escape sequences:
   https://gist.github.com/fnky/458719343aabd01cfb17a3a4f7296797 *)

let bold ppv ppf x =
  Format.fprintf ppf "@<0>%s%a@<0>%s" "\027[1m" ppv x "\027[0m"

let bold_red ppv ppf x =
  Format.fprintf ppf "@<0>%s%a@<0>%s" "\027[1;31m" ppv x "\027[0m"

let bold_red_bg ppv ppf x =
  Format.fprintf ppf "@<0>%s%a@<0>%s" "\027[1;41m" ppv x "\027[0m"

let red ppv ppf x =
  Format.fprintf ppf "@<0>%s%a@<0>%s" "\027[31m" ppv x "\027[0m"

let located_exception_printer cause_printer locations =
  try
    let snippets = make_location_snippets (List1.to_list locations) in
    if List.length snippets > 0 then
      let pp_snippet ppf (location, lines) =
        Format.fprintf ppf "@[<v 0>@[%a@]:@,%a@]" (bold Location.pp) location
          (List.pp ~pp_sep:Format.pp_print_cut (fun ppf (line, carets) ->
               Format.fprintf ppf "%s@,%a" line
                 (red Format.pp_print_string)
                 carets))
          lines
      in
      Format.dprintf "@[<v 0>%a@,@[<hov 0>%a %t@]@]"
        (List.pp ~pp_sep:Format.pp_print_cut pp_snippet)
        snippets
        (bold_red Format.pp_print_string)
        "Error:" cause_printer
    else
      (* All locations in [locations] are ghost locations. *)
      Format.dprintf "@[<v 0>%a @[%t@]@]"
        (bold_red Format.pp_print_string)
        "Error:" cause_printer
  with
  | _ ->
      (* An exception occurred while trying to read the snippets. Report the
         exception without the snippets. *)
      Format.dprintf "@[<v 0>%a@,@[%t@]@]"
        (List1.pp ~pp_sep:Format.pp_print_cut (fun ppf location ->
             Format.fprintf ppf "@[%a@]" Location.pp location))
        locations cause_printer

(** [find_printer_or_fallback cause] attempts to find a printer for [cause],
    and otherwise returns a printer using {!Printexc.to_string_default}. *)
let find_printer_or_fallback cause =
  match find_printer_opt cause with
  | Option.Some printer -> printer
  | Option.None -> Format.dprintf "%s" (Printexc.to_string_default cause)

let () =
  register_exception_printer (function
    | Located_exception { cause; locations } ->
        located_exception_printer (find_printer_or_fallback cause) locations
    | Composite_exception { causes } ->
        Format.dprintf "@[<v 0>%a@]"
          (List2.pp ~pp_sep:Format.pp_print_cut (fun ppf printer ->
               Format.fprintf ppf "@[%t@]" printer))
          (List2.map find_printer_or_fallback causes)
    | Aggregate_exception { exceptions } ->
        Format.dprintf "@[<v 0>%a@]"
          (List2.pp
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,@,")
             (fun ppf printer -> Format.fprintf ppf "@[%t@]" printer))
          (List2.map find_printer_or_fallback exceptions)
    | Not_implemented msg ->
        Format.dprintf "@[<hov 0>%a Please report this as a bug.@ %s@]"
          (bold_red_bg Format.pp_print_string)
          "Not implemented." msg
    | Sys_error msg ->
        Format.dprintf "@[<v 0>%a %s@]"
          (bold_red Format.pp_print_string)
          "System error:" msg
    | Violation msg ->
        Format.dprintf "@[<hov 0>%a Please report this as a bug.@ %s@]"
          (bold_red_bg Format.pp_print_string)
          "Internal error." msg
    | cause -> raise_unsupported_exception_printing cause)

let () =
  Printexc.register_printer (fun exn ->
      match find_printer_opt exn with
      | Option.Some printer ->
          Option.some (Format.asprintf "@[<v 0>%t@]@." printer)
      | Option.None -> Option.none)

let () =
  Printexc.set_uncaught_exception_handler (fun exn backtrace ->
      let exn_printer =
        match find_printer_opt exn with
        | Option.Some printer -> Format.dprintf "@[<v 0>%t@]@." printer
        | Option.None ->
            if Printexc.backtrace_status () then
              (* [backtrace] is non-empty. *)
              Format.dprintf
                "@[<hov 0>%a@ Please report this as a bug.@ %s@ %s@]@."
                (bold_red_bg Format.pp_print_string)
                "Uncaught exception:"
                (Printexc.to_string_default exn)
                (Printexc.raw_backtrace_to_string backtrace)
            else
              (* [backtrace] is empty since bracktrace recording was not
                 enabled. *)
              Format.dprintf
                "@[<hov 0>%a@ Please report this as a bug.@ %s@]@."
                (bold_red_bg Format.pp_print_string)
                "Uncaught exception:"
                (Printexc.to_string_default exn)
      in
      exn_printer Format.err_formatter)
