open Support
open Beluga_syntax

module Error = struct
  type t =
    | EndOfInput (** Any user prompt is subject to raise this error *)

  exception E of t

  let error_printer = function
    | EndOfInput ->
       Format.dprintf "End of input."

  let () =
    Error.register_exception_printer (function
      | E e -> error_printer e
      | exn -> Error.raise_unsupported_exception_printing exn)

  let throw e = raise (E e)
end

type t =
  { prompt : InputPrompt.t
  ; mutable prompt_number : int
  ; ppf : Format.formatter
  }

let prompt_number io = io.prompt_number

let formatter io = io.ppf

let printf io x = Format.fprintf io.ppf x

let make prompt ppf =
  { prompt; ppf; prompt_number = 0 }

let[@warning "-32"] next_prompt_number io =
  io.prompt_number <- io.prompt_number + 1;
  io.prompt_number

let default_prompt_source = "<prompt>"

let[@warning "-39"] rec parsed_prompt ?(source = default_prompt_source) io ~msg ~history_file p =
  match io.prompt ~msg ~history_file () with
  | Option.None -> Error.(throw EndOfInput)
  | Option.Some line -> Obj.magic () (* TODO: Parse only [p] on [line] *)
