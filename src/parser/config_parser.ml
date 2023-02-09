open Support
open Beluga_syntax

let shift_position position c =
  Stdlib.Lexing.{ position with pos_cnum = position.pos_cnum + c }

let rec tokenize_configuration_file lexer_buffer =
  match%sedlex lexer_buffer with
  | eof -> Option.none
  | '%', Star (Compl '\n')
  | white_space ->
      tokenize_configuration_file lexer_buffer
  | _ -> tokenize_file_path lexer_buffer

and tokenize_file_path lexer_buffer =
  match%sedlex lexer_buffer with
  | any, Star (Intersect (Compl '\n', Compl eof)) ->
      let raw_file_path = Sedlexing.Utf8.lexeme lexer_buffer in
      (* Trim whitespaces on the right *)
      let trimmed_file_path = String.trim raw_file_path in
      let start_position, stop_position =
        Sedlexing.lexing_positions lexer_buffer
      in
      (* Adjust the stop position to match the trimmed file path *)
      let stop_position' =
        shift_position stop_position
          (String.length trimmed_file_path - String.length raw_file_path)
      in
      let filename = start_position.Lexing.pos_fname in
      let location =
        Location.make_from_lexing_positions ~filename ~start_position
          ~stop_position:stop_position'
      in
      Option.some (location, trimmed_file_path)
  | _ -> assert false

let read_configuration_file ~filename =
  In_channel.with_open_bin filename (fun in_channel ->
      let lexer_buffer = Sedlexing.Utf8.from_channel in_channel in
      Sedlexing.set_filename lexer_buffer filename;
      Sedlexing.set_position lexer_buffer
        { Lexing.pos_fname = filename
        ; pos_lnum = 1
        ; pos_bol = 0
        ; pos_cnum = 0
        };
      let tokens_seq =
        Seq.of_gen (fun () -> tokenize_configuration_file lexer_buffer)
      in
      (* Consume the token sequence *)
      try Seq.to_list tokens_seq with
      | cause ->
          In_channel.close_noerr in_channel;
          Error.raise cause)

let read_configuration_file_paths ~filename =
  let dir = Filename.dirname filename in
  let paths = read_configuration_file ~filename in
  List.map
    (fun (location, path) ->
      let path' = Filename.concat dir path in
      (location, path'))
    paths

let is_configuration_file ~filename = Filename.check_suffix filename ".cfg"

let rec recursively_read_configuration_file_paths ~filename =
  let paths = read_configuration_file_paths ~filename in
  List.concat_map
    (fun (location, filename) ->
      if is_configuration_file ~filename then
        recursively_read_configuration_file_paths ~filename
      else [ (location, filename) ])
    paths

let read_configuration ~filename =
  if is_configuration_file ~filename then
    recursively_read_configuration_file_paths ~filename
  else [ (Location.ghost, filename) ]
