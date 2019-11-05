open Support

type filename = string

let parse_gen (filename : filename) g (p : 'a Parser.t) : Parser.state * 'a Parser.result =
  let l = Lexer.mk (Location.initial filename) g |> LinkStream.of_gen in
  Parser.run p (Parser.initial_state l)

let parse_file (filename : filename) (p : 'a Parser.t) : Parser.state * 'a Parser.result =
  Gen.IO.with_in filename (fun g -> parse_gen filename g p)

let parse_channel (filename : filename) (chan : in_channel) (p : 'a Parser.t)
    : Parser.state * 'a Parser.result =
  parse_gen filename (GenMisc.of_in_channel chan) p

let parse_string (filename : filename) (input : string) (p : 'a Parser.t)
    : Parser.state * 'a Parser.result =
  parse_gen filename (GenMisc.of_string input) p
