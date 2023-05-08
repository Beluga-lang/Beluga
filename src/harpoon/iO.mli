(** Centralizes high-level Harpoon input-output capabilities. *)

open Beluga_syntax

exception Io_error of exn

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

(** [read_line ?source io ~msg ~history_file] prompts the user for input by
    displaying the given message. The input line is output. The returned
    location is an empty location having [source] as filename and the number
    of lines input so far as the line number.

    The default value of [?source] is {!val:default_source_prompt}.

    An exception is raised if there are no more lines in the input. *)
val read_line :
     ?source:string
  -> t
  -> msg:string
  -> history_file:string option
  -> Location.t * string

(** [prompt_input ?source io ~msg ~history_file f] repeatedly prompts the
    user for an input to pass to [f] until a call to [f] does not throw. That
    is, it calls [read_line ?source io ~msg ~history_file], then passes the
    result to [f]. If [f] raises an exception, then it is caught, printed,
    and [prompt_input] is called once more.

    Make sure that [f] can fail gracefully (by cleaning up in case of a
    raised exception) because any exception from [f] will be suppressed. *)
val prompt_input :
     ?source:string
  -> t
  -> msg:string
  -> history_file:string option
  -> (Location.t -> string -> 'a)
  -> 'a
