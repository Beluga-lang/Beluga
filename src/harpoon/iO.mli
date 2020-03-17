(** Centralizes high-level Harpoon input-output capabilities. *)

module Error : sig
  type t =
    | EndOfInput (** Any prompt is subject to raising this. *)

  (** Formats an error. *)
  val fmt_ppr : Format.formatter -> t -> unit

  exception E of t
end

(** Type of IO capabilities. Includes:
    - prompting the user for input,
    - displaying a message to the user.

    When a function needs user interactivity, pass this object to it.
    If it only needs an output capability, see {!formatter}.
  *)
type t

(** Constructs an IO capability. *)
val make : InputPrompt.t -> Format.formatter -> t

(** Extracts the formatter from an IO capability. *)
val formatter : t -> Format.formatter

(** Gets the number of the last prompt that was shown. *)
val prompt_number : t -> int

(** Displays a formatted message. *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

(** Default value used for the filename when displaying parse
    errors. *)
val default_prompt_source : string

(** Prompts the user for input by displaying the given message.
    The response is parsed using the given parser.
    In case of parse errors, the prompt is repeated.

    To allow the user to abort the loop, use a parser that accepts the
    empty string. See {!Parser.maybe}.

    The default value of the optional `source` parameter is
    {!default_source_prompt}.
 *)
val parsed_prompt : ?source : string ->
                    t ->
                    string -> string option ->
                    'a Beluga.Parser.t ->
                    'a
