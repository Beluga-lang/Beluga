include module type of Stdlib.Format

type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

val stringify : (formatter -> 'a -> unit) -> 'a -> string

val punctuation : string -> formatter -> unit -> unit

val semicolon : formatter -> unit -> unit

val comma : formatter -> unit -> unit

(** [pp_utf_8 ppf s] prints in state [ppf] the UTF-8 encoded string [s] with
    correct handling of codepoint lengths. For instance, if [s = "→"], then
    [pp_print_string ppf s] prints [s] as a string of length [3], whereas
    [pp_utf_8 ppf s] prints [s] as a string of length [1]. *)
val pp_utf_8 : formatter -> string -> unit

(** [pp_utf_8_text ppf s] is analogous to {!pp_print_text} for a UTF-8
    encoded string [s] with correct handling of codepoint lengths. *)
val pp_utf_8_text : formatter -> string -> unit
