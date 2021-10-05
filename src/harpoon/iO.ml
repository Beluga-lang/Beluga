open Support
open Beluga
open Syntax

module Error = struct
  type t =
    | EndOfInput (** Any user prompt is subject to raise this error *)

  exception E of t

  open Format

  let fmt_ppr ppf = function
    | EndOfInput ->
       fprintf ppf "End of input."

  let _ =
    Error.register_printing_function
      (function E e -> Some e | _ -> None)
      fmt_ppr

  let throw e = raise (E e)
end

type t =
  { prompt : InputPrompt.t
  ; prompt_number : int ref
  ; ppf : Format.formatter
  }

let prompt_number io = ! (io.prompt_number)

let formatter io = io.ppf

let printf io x = Format.fprintf io.ppf x

let make prompt' ppf =
  let prompt_number = ref 0 in
  (* instrument the InputPrompt.t so that every successful call
     increments the prompt number *)
  let prompt x y () =
    let open Option in
    prompt' x y () $> fun x -> incr prompt_number; x
  in
  { prompt; ppf; prompt_number }

let next_prompt_number io = incr io.prompt_number; !(io.prompt_number)

let default_prompt_source = "<prompt>"

let rec parsed_prompt ?(source = default_prompt_source) io msg use_history (p : 'a Parser.t) : 'a =
  match io.prompt msg use_history () with
  | None -> Error.(throw EndOfInput)
  | Some line ->
     Runparser.parse_string
       (Loc.(move_line (next_prompt_number io) (initial source)))
       line
       (Parser.only p)
     |> snd
     |> Parser.handle
          begin fun err ->
          printf io "@[%a@]@."
            Parser.print_error err;
          parsed_prompt io msg use_history p
          end
          Fun.id
