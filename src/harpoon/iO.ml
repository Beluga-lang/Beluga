open Support
open Beluga_syntax

exception End_of_input

exception Io_error of exn

let () =
  Error.register_exception_printer (function
    | End_of_file -> Format.dprintf "End of input."
    | Io_error e -> Error.find_printer e
    | exn -> Error.raise_unsupported_exception_printing exn)

let raise_io_error e = Error.raise (Io_error e)

type t =
  { prompt : InputPrompt.t
  ; mutable prompt_number : int
  ; ppf : Format.formatter
  }

let prompt_number io = io.prompt_number

let formatter io = io.ppf

let printf io x = Format.fprintf io.ppf x

let make prompt ppf = { prompt; ppf; prompt_number = 0 }

let next_prompt_number io =
  io.prompt_number <- io.prompt_number + 1;
  io.prompt_number

let default_prompt_source = "<prompt>"

let read_line ?(source = default_prompt_source) io ~msg ~history_file =
  match InputPrompt.next_line_opt ~msg ~history_file io.prompt with
  | Option.None -> raise_io_error End_of_input
  | Option.Some line ->
      let prompt_number = next_prompt_number io in
      let location =
        Location.set_start_line prompt_number (Location.initial source)
      in
      (location, line)
