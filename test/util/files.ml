open Support
open Beluga_syntax

type test_case_token =
  | Input of string
  | Terminator

let rec tokenize_test_cases lexer_buffer =
  match%sedlex lexer_buffer with
  | eof -> Option.none
  | '%', Star (Compl '\n')
  | white_space ->
      tokenize_test_cases lexer_buffer
  | ";;" -> Option.some Terminator
  | _ -> tokenize_test_case lexer_buffer

and tokenize_test_case lexer_buffer =
  match%sedlex lexer_buffer with
  | any, Star (Compl ';'), Star (';', Plus (Compl ';')) ->
      let input = Sedlexing.Utf8.lexeme lexer_buffer in
      Option.some (Input input)
  | _ -> assert false

exception Extraneous_test_case_terminator

exception Unterminated_test_case

let parse_test_cases =
  let rec parse_test_cases_tl tokens acc =
    match tokens with
    | (location, Input input) :: (_location, Terminator) :: tokens' ->
        parse_test_cases_tl tokens' ((location, input) :: acc)
    | (location, Terminator) :: _ ->
        Error.raise_at1 location Extraneous_test_case_terminator
    | (_, Input _) :: (_, Input _) :: _ ->
        Error.raise_violation "Unexpectedly split a test case in two"
    | (location, Input _) :: [] ->
        Error.raise_at1 location Unterminated_test_case
    | [] -> List.rev acc
  in
  fun tokens -> parse_test_cases_tl tokens []

let convert_token_location filename = function
  | Option.None, _start_position, _stop_position -> Option.none
  | Option.Some token, start_position, stop_position ->
      let location =
        Location.make_from_lexing_positions ~filename ~start_position
          ~stop_position
      in
      Option.some (location, token)

let read_test_case_inputs ~filename =
  let tokens =
    In_channel.with_open_bin filename (fun in_channel ->
        let lexer_buffer = Sedlexing.Utf8.from_channel in_channel in
        let generate_token =
          Sedlexing.with_tokenizer tokenize_test_cases lexer_buffer
        in
        let tokens_seq =
          Seq.of_gen (fun () ->
              let token = generate_token () in
              convert_token_location filename token)
        in
        (* Consume the token sequence *)
        try Seq.to_list tokens_seq with
        | cause ->
            In_channel.close_noerr in_channel;
            raise cause)
  in
  parse_test_cases tokens

(** {2 Exception Printing} *)

let () =
  Error.register_exception_printer (function
    | Extraneous_test_case_terminator ->
        Format.dprintf "%a" Format.pp_print_text
          "Extraneous test case terminator."
    | Unterminated_test_case ->
        Format.dprintf "%a" Format.pp_print_text "Unterminated test case."
    | exn -> Error.raise_unsupported_exception_printing exn)
