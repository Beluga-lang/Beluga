(**
Replay is the test harness for the Beluga interactive mode.
Replay processes _interaction transcripts_, which are files defined by
the following informal grammar:

  * A valid Beluga program, (followed by a line break,) hereafter
    referred to as the _input program_.
  * One or more _interactions_.

where each _interaction_ consists of:

  * A _request_, which is an interactive mode command, of the form
    `%:FOO ...`.
  * A _response_, which is an arbitrary block of text, beginning on
    its own line, up to the next request.

What Replay does with _interaction transcripts_ is the following:

  * The _input program_ is written to a file called `input.bel`.
  * A Beluga interactive subprocess is spawned under the control of
    Replay, with the command `beluga -I -emacs`.
  * For each _interaction_ present in the _interaction transcript_:
      * The _request_ is sent to the Beluga subprocess.
      * The output generated by the subprocess is compared with the
        _response_ associated with the _request_.
      * Additionally, the output generated by the subprocess is
        written to the file `last-output.bel`.
      * Should they differ, Replay exits with a nonzero status.
 *)

open Support

(**
An interaction consists of a _request_, which is sent to the
subprocess, and a response, which is compared with the output
generated by the subprocess in response to the request.
 *)
type interaction =
  { request : string;
    response : string;
    line_num : int option;
  }

(**
A transcript consists of an input file, which is valid Beluga code, followed by a number of interactions.
 *)
type transcript =
  { input_file : string;
    interactions : interaction list;
  }

module TranscriptParser = struct
  module Parser = Mupc.StringParser

  module Tokenizer = Tokenizer.ForParser (Parser)

  type 'a parser = 'a Parser.t

  open Parser

  (** A parser for the interactive mode command sigil `%:` *)
  let sigil : string parser = label "command sigil" (string "%:")

  let bol_sigil : string parser = bol >>= fun _ -> sigil

  (** A parser for an interactive mode command, which is a line
  beginning with a sigil. *)
  let command : string parser =
    label "command"
      ( trying bol_sigil
        >>= fun _ ->
          many_till any (void (trying (string "\n"))) $>
            String.pack $>
            fun s -> "%:" ^ s ^ "\n" )

  (** A parser for an interaction: a command followed by an expected
  response. *)
  let interaction : interaction parser =
    label "interaction"
      ( get_line
        >>= fun line_num ->
          command
          >>= fun cmd ->
            many_till any (trying (lookahead (alt (void bol_sigil) eof))) $>
              String.pack $>
              fun resp ->
                { request = cmd;
                  response = resp;
                  line_num = Some line_num;
                } )

  (** A parser for a transcript: an input file followed by a number of
  interactions. *)
  let transcript : transcript parser =
    label "beluga test transcript"
      begin
        let p =
          many_till any (void (trying (lookahead bol_sigil))) in
        label "input beluga code" p $> String.pack
        >>= fun bel ->
          let f ints =
            { input_file = bel;
              interactions = ints;
            }
          in
          map f (label "interactions block" (some interaction))
          >>= fun trans -> eof $> fun _ -> trans
      end

  let parse_transcript (input : char Token.t Parser.Stream.t) :
        state * (parse_error, transcript) Either.t =
    parse transcript (initialize input)
end

module TranscriptRunner = struct
  module Parser = Mupc.StringParser
  module Tokenizer = Tokenizer.ForParser (Parser)

  (** The environment in which the transcript runner executes. *)
  type env =
    { beluga_out : Parser.state;
      beluga_in : out_channel;
    }

  let beluga_command exe = exe ^ " -I -emacs"

  let create_env exe : env =
    let (in_chan, out_chan) = Unix.open_process (beluga_command exe) in
    { beluga_out =
        in_chan |>
          IStream.of_channel |>
          IStream.map (fun c -> Printf.printf "%c" c; flush stdout; c) |>
          Tokenizer.char_tokenize_from Loc.initial |>
          Parser.initialize;
      beluga_in = out_chan;
    }

  let beluga_send (s : string) (env : env) : unit =
    print_string s;
    output_string env.beluga_in s;
    flush env.beluga_in

  (** Reads from the beluga output stream until a semicolon followed
      by a line break is encountered.
   *)
  let beluga_read_response (s : Parser.state) :
        Parser.state * (Parser.parse_error, string) Either.t =
    let open Parser in
    let response =
      many_till any (void (label "semicolon&newline" (trying (string ";\n")))) $>
        String.pack $>
        fun x -> x ^ ";\n"
    in
    parse response s

  (** Send an interactive mode command to the Beluga subprocess
  managed by `env` and read the whole response.
  Beluga terminates responses with the semicolon, so `rpc` will block
  until it reads a semicolon from Beluga.
  The result is Nothing if no response could be parsed.
  *)
  let rpc (request : string) (env : env) : (string * env) option =
    beluga_send request env;
    match beluga_read_response env.beluga_out with
    | (_, Either.Left err) ->
       Printf.printf "parse error: %s\n" (Parser.string_of_parse_error err);
       None
    | (s, Either.Right x) -> Some (x, { env with beluga_out = s } )

  let write_file (path : string) (contents : string) : unit =
    let h = open_out_bin path in
    output_string h contents;
    flush h;
    close_out h

  (** Removes the semicolon from a beluga response. *)
  let drop_semi (str : string) : string =
    (* drop the last two characters (the semicolon and the newline)
    and then stick the newline back on. *)
    String.sub str 0 (String.length str - 2) ^ "\n"

  type string_match =
    | MismatchAt of int
    | LengthDiffers of int * int
    | Equal

  let rec string_match' i (s1 : char list) (s2 : char list) : string_match =
    match s1, s2 with
    | [], [] -> Equal
    | c1 :: s1', c2 :: s2' when c1 = c2 -> string_match' (i + 1) s1' s2'
    | _, _ -> MismatchAt i

  let string_match (s1 : string) (s2 : string) : string_match =
    let l1 = String.length s1 in
    let l2 = String.length s2 in
    match () with
    | () when l1 = l2 ->
       string_match' 0 (String.unpack s1) (String.unpack s2)
    | () -> LengthDiffers (l1, l2)

  let run_interaction (i : interaction) (e : env) :
        (string, env) Either.t =
    let string_of_line : int option -> string =
      Option.eliminate
        (fun () -> "<unknown>")
        string_of_int
    in
    rpc i.request e |>
      Option.eliminate
        (fun () ->
          Either.left
            ( "interaction on line "
              ^ string_of_line i.line_num
              ^ " failed: Beluga subprocess unexpectedly closed "
              ^ "its output channel" )
        )
        (fun (res, e') ->
          match string_match res i.response with
          | Equal ->
              write_file "last-output.bel" (drop_semi res);
              Either.right e'
          | LengthDiffers (l1, l2) ->
             Either.left
               ( "interaction on line "
                 ^ string_of_line i.line_num
                 ^ " failed: length mismatch\n"
                 ^ "response length: " ^ string_of_int l1 ^ "\n"
                 ^ "expected length: " ^ string_of_int l2 ^ "\n"
               )
          | MismatchAt n ->
             Either.left
               ( "interaction on line "
                 ^ string_of_line i.line_num
                 ^ " failed: output mismatch at byte " ^ string_of_int n ^ "\n"
                 ^ "expected output:\n"
                 ^ i.response
                 ^ "actual output:\n"
                 ^ res )
        )
    let rec run_interactions (ints : interaction list) (e : env) :
          (string, env) Either.t =
    let open Either in
    match ints with
    | [] -> Either.right e
    | (i :: ints) ->
       run_interaction i e
       >>= fun e' ->
         run_interactions ints e'

  let run_transcript (transcript : transcript) (e : env) : (string, env) Either.t =
    write_file "input.bel" transcript.input_file;
    run_interactions transcript.interactions e
end

type error =
  | ParseError of string
  | InteractionError of string

let main () =
  let real_main () : (error, TranscriptRunner.env) Either.t =
    let exe = Array.get Sys.argv 1 in
    let path = Array.get Sys.argv 2 in
    let input_chan = open_in path in
    let input = input_chan |> IStream.of_channel |> TranscriptParser.Tokenizer.char_tokenize_from Loc.initial in
    let open Either in
    TranscriptParser.parse_transcript input |>
      Pair.snd |>
      Either.map_left
        (fun e ->
          TranscriptParser.Parser.string_of_parse_error e |>
            fun x -> ParseError x)
      >>= fun transcript ->
      let open TranscriptRunner in
      let env = create_env exe in
      run_transcript transcript env |>
        Either.map_left (fun e -> InteractionError e)
  in
  real_main () |>
    Either.eliminate
      ( function
        | ParseError err ->
           print_string "parse error: ";
           print_string err;
           exit 1
        | InteractionError err ->
           print_string err;
           exit 1 )
      ( fun _ -> exit 0 )

let _ =
  try
    main ()
  with
  | e ->
     Printexc.print_backtrace stdout;
     print_string (Printexc.to_string e)
