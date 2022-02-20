(** Option parser errors. *)
module Error : sig
  module Option : sig
    type option_error = { option_name : string }
  end

  module Argument : sig
    type invalid_arguments_length_error =
      { option_name : string
      ; expected_argument_count : int
      ; actual_argument_count : int
      }
  end

  (** The type of CLI arguments parsing errors. *)
  type t =
    [ `Missing_mandatory_option of Option.option_error
      (** Missing mandatory option for invoking the CLI command *)
    | `Invalid_arguments_length of Argument.invalid_arguments_length_error
      (** Mismatched number of arguments to an option *)
    | `Argument_reader_failure of Option.option_error
      (** Failure to read an argument to an option from a string *)
    | `Not_an_option of Option.option_error
      (** Unrecognized option provided *)
    ]
end

module HelpEntry : sig
  type t =
    { option_name : OptName.t
    ; arguments : string list
    ; help_message : string option
    }
end

(** The type for formatting the mandatory and optional options of an options
    specification. The first argument passed to a [help_printer] is the
    example usage of the command. *)
type help_printer = string -> Format.formatter -> unit -> unit

(** The type of specification for multiple command-line options. ['a] is the
    type of value to be parsed from a list of arguments matching their
    respective specifications. *)
type +'a t

val find_opt :
     'a t
  -> string
  -> (int option * (help_printer -> string list -> unit)) option

val get_comp_value : 'a t -> string list -> ('a, Error.t) result

val get_mandatory_help_entries : 'a t -> HelpEntry.t list

val get_optional_help_entries : 'a t -> HelpEntry.t list

(** [opt0 arg infos] defines an option with no extra arguments and using
    [infos]. When the option is input in the CLI and parsed, then [arg] is
    returned.

    For defining a boolean switch option, see {!switch_opt}. *)
val opt0 : 'a -> 'a OptInfo.Unchecked.transform list -> 'a t

(** [opt1 arg_parser infos] defines a unary option using [infos]. When the
    option is input in the CLI and parsed, the extra argument is parsed by
    [arg_parser]. *)
val opt1 :
  (string -> 'a option) -> 'a OptInfo.Unchecked.transform list -> 'a t

(** [bool_opt1 infos] defines a unary boolean option using [infos]. The extra
    argument to be input in the CLI is either ["true"] or ["false"]. *)
val bool_opt1 : bool OptInfo.Unchecked.transform list -> bool t

(** [int_opt1 infos] defines a unary integer option using [infos]. *)
val int_opt1 : int OptInfo.Unchecked.transform list -> int t

(** [int_opt1 infos] defines a unary string option using [infos]. *)
val string_opt1 : string OptInfo.Unchecked.transform list -> string t

(** [switch_opt infos] defines a switch option with no extra argument and
    using [infos]. If the option is input in the CLI, then this option is
    parsed with value [true], and [false] otherwise. As such, switch options
    are not required.

    The default arguments specified by {!default_argument} and {!optional} in
    [infos] are discarded. *)
val switch_opt : bool OptInfo.Unchecked.transform list -> bool t

(** [takes_all_opt infos] defines an option taking all subsequent arguments,
    including the arguments prefixed with ['-']. *)
val takes_all_opt :
  string list OptInfo.Unchecked.transform list -> string list t

(** [impure_opt0 handler infos] defines an option with no argument and using
    [infos] that calls [handler] when the option is provided.

    This is typically used with a handler of type [unit -> unit] and {!(<!)}
    for discarding the parsed unit. *)
val impure_opt0 : (unit -> 'a) -> 'a OptInfo.Unchecked.transform list -> 'a t

(** [help_opt0 help_handler infos] defines an option with no argument and
    using [infos] that calls [help_handler] with the options specification's
    {!help_printer}.

    This is typically used with {!(<!)} for discarding the parsed unit. *)
val help_opt0 :
  (help_printer -> 'a) -> 'a OptInfo.Unchecked.transform list -> 'a t

(** [rest_args handler] defines a handler for {i leftover arguments} provided
    to the CLI command. A {i leftover argument} is

    - an argument before any options,
    - an argument after all options,
    - an argument between options but not handled by one of them. *)
val rest_args : (string list -> unit) -> unit t

(** The [map] function of the ['a t] functor.

    This is used for transforming parsed options.*)
val ( <$ ) : ('a -> 'b) -> 'a t -> 'b t

(** {!(<$)} with its arguments flipped. *)
val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

(** The [ap] function of the ['a t] applicative.

    This is used to add an option to a pre-existing options specification. *)
val ( <& ) : ('a -> 'b) t -> 'a t -> 'b t

(** [spec <! spec'] adds specification [spec'] to [spec] and discards the
    result of parsing against [spec'].

    This is used for adding impure behavior to parsing. *)
val ( <! ) : 'a t -> unit t -> 'a t
