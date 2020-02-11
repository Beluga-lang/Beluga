open Support

type filename = string

let parse_gen loc g (p : 'a Parser.t) : Parser.state * 'a Parser.result =
  let l = Lexer.mk loc g |> LinkStream.of_gen in
  Parser.run p (Parser.initial_state l)

let parse_file loc (p : 'a Parser.t) : Parser.state * 'a Parser.result =
  Gen.IO.with_in (Location.filename loc) (fun g -> parse_gen loc g p)

let parse_channel loc (chan : in_channel) (p : 'a Parser.t)
    : Parser.state * 'a Parser.result =
  parse_gen loc (GenMisc.of_in_channel chan) p

let parse_string loc (input : string) (p : 'a Parser.t)
    : Parser.state * 'a Parser.result =
  parse_gen loc (GenMisc.of_string input) p
