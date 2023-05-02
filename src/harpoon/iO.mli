(** Centralizes high-level Harpoon input-output capabilities. *)

open Beluga_syntax

type exn += private Io_error of exn

(** Type of IO capabilities. Includes:

    - prompting the user for input,
    - displaying a message to the user.

    When a function needs user interactivity, pass this object to it. If it
    only needs an output capability, see {!type:Format.formatter}. *)
type t

(** Constructs an IO capability. *)
val make : InputPrompt.t -> Format.formatter -> t

(** Extracts the formatter from an IO capability. *)
val formatter : t -> Format.formatter

(** Gets the number of the last prompt that was shown. *)
val prompt_number : t -> int

(** Displays a formatted message. *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

(** Default value used for the filename when displaying parse errors. *)
val default_prompt_source : string

(** Prompts the user for input by displaying the given message. The input
    line is output.

    The default value of the optional `source` parameter is
    {!default_source_prompt}. *)
val read_line :
     ?source:string
  -> t
  -> msg:string
  -> history_file:string option
  -> Location.t * string
