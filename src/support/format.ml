include Stdlib.Format

(** Polymorphic function that processes a format string. *)
type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

(** Converts something to a string using a formatting function. *)
let stringify p x = asprintf "%a" p x

(** Prints the given string followed by a space break hint. *)
let punctuation s ppf () = fprintf ppf "%s@ " s

(** Prints a semicolon followed by a space break hint. *)
let semicolon = punctuation ";"

(** Prints a comma followed by a space break hint. *)
let comma = punctuation ","

let between before after inside ppf () =
  before ppf ();
  inside ppf ();
  after ppf ()
