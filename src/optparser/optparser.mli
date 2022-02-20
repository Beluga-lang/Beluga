(** Command-line interface (CLI) command options specification and parser.

    [Optparser] is a library for specifying an expected format for CLI
    command options, and for parsing the CLI arguments against that
    specification.

    @author Clare Jang *)

(** {1 Specification for an Option} *)

(** The type of specification for a command-line option. ['a] is the type of
    value to be parsed from an argument matching the specification. *)
type +'a option_specification

(** The type of step in specifying an option for ['a option_specification]. *)
type 'a option_specification_step

(** The type of steps in specifying an option for ['a option_specification].
    The steps are declared in order, such that later specification steps
    override earlier ones if they specify the same specification attributes. *)
type 'a option_specification_steps = 'a option_specification_step list

(** {2 Constructors} *)

(** Option specifications are constructed in steps.

    For instance, the build steps for an option [--signature=WORD] with
    [WORD] being a meta-variable of type string for a path and with alias
    [-s] are as follows:

    {[
      [ long_name "signature"
      ; short_name 's'
      ; meta_variables [ "path" ]
      ; help_message "specify the path to the signature file"
      ]
    ]}

    Options are required to have a long name or a short name, otherwise an
    internal error is raised.

    An option and their argument can be made not required separately.

    For instance, the [--debug] option below is specified as not required,
    with a default argument if it used without one.

    - If [--debug] is not used, then ["/tmp/debug.out"] is used as path.
    - If [--debug] is used without a [path] argument, then ["./debug.out"] is
      used as path.

    {[
      [ long_name "debug"
      ; meta_variables [ "path" ]
      ; default_argument "./debug.out"
      ; optional "/tmp/debug.out"
      ]
    ]}

    In contrast, the [--signature] option below is not required, but if it is
    used then the ["path"] argument is required.

    {[
      [ long_name "signature"
      ; meta_variables [ "path" ]
      ; optional "./sources.cfg"
      ]
    ]} *)

(** [long_name name] constructs the specification step for an option having a
    string name [name]. In the CLI, [name] is prefixed by ["--"].

    For example, an option having [long_name "abc"] has [--abc] as the actual
    CLI option name. *)
val long_name : string -> 'a option_specification_step

(** [short_name name] constructs the specification for an option having a
    short name [name]. In the CLI, [name] is prefixed by ["-"].

    For example, an option having [short_name 's'] has [-s] as the actual CLI
    option name. *)
val short_name : char -> 'a option_specification_step

(** [other_names aliases] constructs the specification for an option having
    the aliases [aliases]. In the CLI, the aliases in [aliases] are used
    as-is, meaning that the user must exactly specify ony of them,

    For example, an option having
    [other_names \["signature"; "--signature"\]] may be referred to as
    [signature] or [--signature] in the CLI. *)
val other_names : string list -> 'a option_specification_step

(** [help_message help] constructs the specification for an option having
    [help] as help message. In the CLI, [help] is displayed when the command
    is invoked with the help option.

    A help option is created using {!help_opt0}. *)
val help_message : string -> 'a option_specification_step

(** [default_argument arg] constructs the specification for an option having
    [arg] as default argument. This default argument is used when the option
    accepts an argument but none is provided.

    The user may still be required to input the option flag, but the argument
    to the option is not required. To make the option itself not required,
    see {!optional}. *)
val default_argument : 'a -> 'a option_specification_step

(** [meta_variables vars] constructs the specification for an option having
    [vars] as hint meta-variables to be displayed in the help message. By
    default, the meta name is ["args"].

    For example, the following option specification uses meta-name ["path"]
    for the only argument to the [--signature] option.

    {[
      [ long_name "signature"
      ; meta_variables [ "path" ]
      ; help_message "specify the path to the signature file"
      ]
    ]}

    In this case, the command is displayed as

    {v --signature path specify the path to the signature file v}

    when the command is invoked with the help option.

    A help option is created using {!help_opt0}. *)
val meta_variables : string list -> 'a option_specification_step

(** [optional arg] constructs the specification for an option that is not
    required. If the command is invoked without the option, then [arg] is
    used as the parsed value.

    The user may still be required to input an argument if they explicitly
    use the option. To make that argument itself not required, see
    {!default_argument}. *)
val optional : 'a -> 'a option_specification_step

(** {1 Specification for Multiple Options} *)

(** The type of specification for multiple command-line options. ['a] is the
    type of value to be parsed from a list of arguments matching their
    respective specifications. *)
type +'a options_specification

(** {2 Constructors} *)

(** Each option in an options set is constructed as a singleton set, and then
    theses sets are combined using the operators in section {!combinators}. *)

(** [opt0 arg infos] defines an option with no extra arguments and using
    [infos]. When the option is input in the CLI and parsed, then [arg] is
    returned.

    For defining a boolean switch option, see {!switch_opt}. *)
val opt0 : 'a -> 'a option_specification_steps -> 'a options_specification

(** [opt1 arg_parser infos] defines a unary option using [infos]. When the
    option is input in the CLI and parsed, the extra argument is parsed by
    [arg_parser]. *)
val opt1 :
     (string -> 'a option)
  -> 'a option_specification_steps
  -> 'a options_specification

(** [bool_opt1 infos] defines a unary boolean option using [infos]. The extra
    argument to be input in the CLI is either ["true"] or ["false"]. *)
val bool_opt1 : bool option_specification_steps -> bool options_specification

(** [int_opt1 infos] defines a unary integer option using [infos]. *)
val int_opt1 : int option_specification_steps -> int options_specification

(** [int_opt1 infos] defines a unary string option using [infos]. *)
val string_opt1 :
  string option_specification_steps -> string options_specification

(** [switch_opt infos] defines a switch option with no extra argument and
    using [infos]. If the option is input in the CLI, then this option is
    parsed with value [true], and [false] otherwise. As such, switch options
    are not required.

    The default arguments specified by {!default_argument} and {!optional} in
    [infos] are discarded. *)
val switch_opt :
  bool option_specification_steps -> bool options_specification

(** [impure_opt0 handler infos] defines an option with no argument and using
    [infos] that calls [handler] when the option is provided.

    This is typically used with a handler of type [unit -> unit] and {!(<!)}
    for discarding the parsed unit. *)
val impure_opt0 :
  (unit -> 'a) -> 'a option_specification_steps -> 'a options_specification

(** The type for formatting the mandatory and optional options of an options
    specification. The first argument passed to a [help_printer] is the
    example usage of the command. *)
type help_printer = string -> Format.formatter -> unit -> unit

(** [help_opt0 help_handler infos] defines an option with no argument and
    using [infos] that calls [help_handler] with the options specification's
    {!help_printer}.

    This is typically used with {!(<!)} for discarding the parsed unit. *)
val help_opt0 :
     (help_printer -> 'a)
  -> 'a option_specification_steps
  -> 'a options_specification

(** [takes_all_opt infos] defines an option taking all subsequent arguments,
    including the arguments prefixed with ['-']. *)
val takes_all_opt :
     string list OptInfo.Unchecked.transform list
  -> string list options_specification

(** [rest_args handler] defines a handler for {i leftover arguments} provided
    to the CLI command. A {i leftover argument} is

    - an argument before any options,
    - an argument after all options,
    - an argument between options but not handled by one of them. *)
val rest_args : (string list -> unit) -> unit options_specification

(** {2:combinators Combinators} *)

(** Specifications for sets of options may be combined together using the
    operators in this section.

    For example, consider the following options specification. When CLI
    arguments are parsed against this specification, the arguments to the
    [--input] and [--output] options are strings resolved to files using
    [Filename.resolve]. These values are then mapped to a record of type
    [{ input : string; output : string }]. If the [--debug] flag is provided
    then [handle_debug] is called to toggle debugging as a side effect.
    Likewise, if the [--help] flag is provided, then [handle_help] is called
    to format and print the options' help messages. If there are any extra
    arguments, then the exception [UnexpectedArguments] is raised.

    {[
      (fun input output -> { input; output })
      <$ (string_opt1
            [ long_name "input"
            ; short_name 'i'
            ; meta_variables [ "path" ]
            ; help_message "specify the input path"
            ]
         &> Filename.resolve)
      <& (string_opt1
            [ long_name "output"
            ; short_name 'o'
            ; meta_variables [ "path" ]
            ; help_message "specify the output path"
            ]
         &> Filename.resolve)
      <! impure_opt0 handle_debug
           [ long_name "debug"; help_message "enable debugging" ]
      <! help_opt0 handle_help
           [ long_name "help"
           ; short_name 'h'
           ; help_message "print this message"
           ]
      <! rest_args (function
           | [] -> ()
           | rest -> raise @@ UnexpectedArguments rest)
    ]} *)

(** The [map] function of the ['a options_specification] functor.

    This is used for transforming parsed options.*)
val ( <$ ) :
  ('a -> 'b) -> 'a options_specification -> 'b options_specification

(** {!(<$)} with its arguments flipped. *)
val ( $> ) :
  'a options_specification -> ('a -> 'b) -> 'b options_specification

(** The [ap] function of the ['a options_specification] applicative.

    This is used to add an option to a pre-existing options specification. *)
val ( <& ) :
     ('a -> 'b) options_specification
  -> 'a options_specification
  -> 'b options_specification

(** [spec <! spec'] adds specification [spec'] to [spec] and discards the
    result of parsing against [spec'].

    This is used for adding impure behavior to parsing. *)
val ( <! ) :
     'a options_specification
  -> unit options_specification
  -> 'a options_specification

(** {1 Options Parser} *)

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

(** [parse spec args] parses [args] using the specification [spec].

    Example usage:

    {[
      let spec = ... in
      let (arg0 :: args) = Array.to_list Sys.argv in
      Optparser.parse spec args
      |> Result.fold ~ok:... ~error:...
    ]} *)
val parse : 'a options_specification -> string list -> ('a, Error.t) result
