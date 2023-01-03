open Support
open Beluga_syntax

let with_pp_to_file filename f =
  let out_channel = Out_channel.open_bin filename in
  try
    let ppf = Format.formatter_of_out_channel out_channel in
    f ppf;
    Format.pp_print_newline ppf ();
    Out_channel.close out_channel
  with
  | cause ->
      Out_channel.close_noerr out_channel;
      raise cause

type test_case_token =
  | Input of string
  | Terminator

let rec tokenize lexer_buffer =
  match%sedlex lexer_buffer with
  | eof -> Option.none
  | '%', Star (Sub (any, ('\n' | eof))), ('\n' | eof)
  | white_space ->
      tokenize lexer_buffer
  | ";;" ->
      let token = Terminator in
      Option.some token
  | ( Plus (Sub (any, ('%' | ';')))
    , Star (';', (eof | Plus (Sub (any, ('%' | ';'))))) ) ->
      let input = Sedlexing.Utf8.lexeme lexer_buffer in
      let token = Input input in
      Option.some token
  | _ -> assert false

exception Unterminated_test_case

let read_test_case_inputs ~filename =
  let in_channel = In_channel.open_bin filename in
  let lexer_buffer = Sedlexing.Utf8.from_channel in_channel in
  let generate_token = Sedlexing.with_tokenizer tokenize lexer_buffer in
  let tokens =
    Seq.of_gen (fun () ->
        match generate_token () with
        | Option.None, _start_position, _stop_position -> Option.none
        | Option.Some token, start_position, stop_position ->
            let location =
              Location.make_from_lexing_positions ~filename ~start_position
                ~stop_position
            in
            Option.some (location, token))
  in
  let input_buffer, _last_location, test_case_inputs =
    try
      Seq.fold_left
        (fun (current_input, previous_location, inputs) token ->
          match token with
          | _location, Terminator ->
              let input = Buffer.contents current_input in
              Buffer.clear current_input;
              let inputs' = (previous_location, input) :: inputs in
              (current_input, Location.ghost, inputs')
          | location, Input input ->
              Buffer.add_string current_input input;
              let location' = Location.join previous_location location in
              (current_input, location', inputs))
        (Buffer.create 16, Location.ghost, [])
        tokens
    with
    | cause ->
        In_channel.close_noerr in_channel;
        raise cause
  in
  In_channel.close in_channel;
  if
    Buffer.length input_buffer = 0
    || String.is_empty (String.trim (Buffer.contents input_buffer))
  then List.rev test_case_inputs
  else raise Unterminated_test_case
