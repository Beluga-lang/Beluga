open Support

module Error = struct
  type t =
    | EndOfInput (** Any user prompt is subject to raise this error *)

  exception E of t

  let error_printer = function
    | EndOfInput ->
       Format.dprintf "End of input."

  let () =
    Beluga_syntax.Error.register_exception_printer (function
      | E e -> error_printer e
      | exn -> Beluga_syntax.Error.raise_unsupported_exception_printing exn)

  let throw e = raise (E e)
end

type t =
  { prompt : InputPrompt.t
  ; prompt_number : int ref
  ; ppf : Format.formatter
  }

let prompt_number io = !(io.prompt_number)

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

let[@warning "-32"] next_prompt_number io = incr io.prompt_number; !(io.prompt_number)

let default_prompt_source = "<prompt>"

let[@warning "-39"] rec parsed_prompt ?(source = default_prompt_source) io msg use_history p =
  match io.prompt msg use_history () with
  | None -> Error.(throw EndOfInput)
  | Some line -> Obj.magic () (* TODO: Parse only [p] on [line] *)
