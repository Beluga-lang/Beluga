module Unchecked : sig
  (** A type built by a user using functions in this module. A value of this
      type will be merged and checked in the functions of {!OptSpec} module. *)
  type +'a t =
    { long_name : string option
    ; short_name : char option
    ; other_names : string list option
    ; meta_variables : string list option
    ; help_message : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }

  val empty : 'a t

  (** A ['a transform] is a function for transforming a {!t}. Transforms can
      be chained starting from {!empty} as in {!make} to construct a {!t} in
      steps. *)
  type 'a transform = 'a t -> 'a t

  (** A function configures the option name that contains more than two
      characters. In command line interface, it will be prepended by ["--"].
      For example, with the input parameter ["abc"], the real CLI option name
      will be [--abc] *)
  val long_name : string -> 'a transform

  (** A function configures the option name that comprises a single
      character. In command line interface, it will be prepended by ["-"].
      For example, with the input parameter ['s'], the real CLI option name
      will be [-s] *)
  val short_name : char -> 'a transform

  (** A function configures the option name that does not start with ["-"] or
      ["--"]. In command line interface, it will be used as-is, so a user
      must specify an exact option name used in CLI. *)
  val other_names : string list -> 'a transform

  (** A function configures the help message for the option. *)
  val help_message : string -> 'a transform

  (** A function configures the default argument of the option. The default
      argument is an argument used when the option accepts an argument but
      none is passed. This function makes only the argument of the option
      optional. To make the option itself, see {!val-optional}. *)
  val default_argument : 'a -> 'a transform

  (** [erase_default_argument spec] reconstructs [spec] without its default
      argument. *)
  val erase_default_argument : 'a transform

  (** A function configures the names of arguments in the help message for
      the option. Default meta name is ["args"]. For example, if [--file]
      option takes one argument, default help message for that option starts
      with [  --file args   ...]. If you want to display [PATH] or
      [TARGET_FILE] instead of [args], pass that name to this function. *)
  val meta_variables : string list -> 'a transform

  (** A function configures whether the option is mandatory or not. A value
      provided to this function is the default value used when a user does
      not pass the option. To make the argument of the option optional
      instead of the option itself, see {!val-default_argument}. *)
  val optional : 'a -> 'a transform

  (** [make ts] makes a {!t} by composing the transforms [ts] and applying
      them to {!empty}. *)
  val make : 'a transform list -> 'a t
end

module Checked : sig
  type +'a t =
    { name : OptName.t
    ; meta_variables : string list
    ; help_message : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }
end

type check_error = [ `No_name ]

val check : 'a Unchecked.t -> ('a Checked.t, [> check_error ]) result
