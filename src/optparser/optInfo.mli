module Unchecked : sig
  (** A type built by a user using functions in this module. A value of this
      type will be merged and checked in the functions of {!OptSpec} module. *)
  type +'a t =
    { long_name : string option
    ; short_name : char option
    ; other_names : string list option
    ; meta_vars : string list option
    ; help_msg : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }

  val empty : 'a t

  (** A function configures the option name that contains more than two
      characters. In command line interface, it will be prepended by ["--"].
      For example, with the input parameter ["abc"], the real CLI option name
      will be [--abc] *)
  val long_name : string -> 'a t

  (** A function configures the option name that comprises a single
      character. In command line interface, it will be prepended by ["-"].
      For example, with the input parameter ['s'], the real CLI option name
      will be [-s] *)
  val short_name : char -> 'a t

  (** A function configures the option name that does not start with ["-"] or
      ["--"]. In command line interface, it will be used as-is, so a user
      must specify an exact option name used in CLI. *)
  val other_names : string list -> 'a t

  (** A function configures the help message for the option. *)
  val help_msg : string -> 'a t

  (** A function configures the default argument of the option. The default
      argument is an argument used when the option accepts an argument but
      none is passed. This function makes only the argument of the option
      optional. To make the option itself, see {!optional}. *)
  val default_argument : 'a -> 'a t

  (** A function configures the names of arguments in the help message for
      the option. Default meta name is ["args"]. For example, if [--file]
      option takes one argument, default help message for that option starts
      with [  --file args   ...]. If you want to display [PATH] or
      [TARGET_FILE] instead of [args], pass that name to this function. *)
  val meta_vars : string list -> 'a t

  (** A function configures whether the option is mandatory or not. A value
      provided to this function is the default value used when a user does
      not pass the option. To make the argument of the option optional
      instead of the option itself, see {!default_argument}. *)
  val optional : 'a -> 'a t

  (** An internal function used in {!OptSpec} module. *)
  val lift : unit t -> 'a t

  val merge : 'a t -> 'a t -> 'a t

  (** An internal function used in {!OptSpec} module.

      @author Clare Jang *)
  val merge_all : 'a t list -> 'a t
end

module Checked : sig
  type +'a t =
    { name : OptName.t
    ; meta_vars : string list
    ; help_msg : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }
end

type check_error = [ `No_name ]

val check : 'a Unchecked.t -> ('a Checked.t, [> check_error ]) result
