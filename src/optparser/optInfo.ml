(** A module for functions to give information for an option. For example,
    functions that configure

    - the name of an option
    - the help message of an option
    - the fallback value of an optional option
    - etc. are included.

    @author Clare Jang *)

(** Unchecked options operations.

    @author Clare Jang *)
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
end = struct
  type 'a t =
    { long_name : string option
    ; short_name : char option
    ; other_names : string list option
    ; meta_vars : string list option
    ; help_msg : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }

  let empty : 'a t =
    { long_name = None
    ; short_name = None
    ; other_names = None
    ; meta_vars = None
    ; help_msg = None
    ; default_argument = None
    ; optional = None
    }


  let long_name ln : 'a t = { empty with long_name = Some ln }

  let short_name sn : 'a t = { empty with short_name = Some sn }

  let other_names ns : 'a t = { empty with other_names = Some ns }

  let help_msg hm : 'a t = { empty with help_msg = Some hm }

  let default_argument (dv : 'a) : 'a t =
    { empty with default_argument = Some dv }


  let meta_vars mvs : 'a t = { empty with meta_vars = Some mvs }

  let optional op : 'a t = { empty with optional = Some op }

  let lift (spec : unit t) : 'a t =
    { spec with default_argument = None; optional = None }


  let merge spec0 spec1 =
    let open Option in
    { long_name = spec0.long_name <|> spec1.long_name
    ; short_name = spec0.short_name <|> spec1.short_name
    ; other_names = spec0.other_names <|> spec1.other_names
    ; meta_vars = spec0.meta_vars <|> spec1.meta_vars
    ; help_msg = spec0.help_msg <|> spec1.help_msg
    ; default_argument = spec0.default_argument <|> spec1.default_argument
    ; optional = spec0.optional <|> spec1.optional
    }


  (* It's not possible to do eta-conversion. By eta-conversion, it loses its
     polymorphicity, and fails to check against its signature *)
  let merge_all specs = List.fold_left merge empty specs
end

module Checked = struct
  type 'a t =
    { name : OptName.t
    ; meta_vars : string list
    ; help_msg : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }
end

type check_error = [ `No_name ]

let check spec =
  ( match (spec.Unchecked.long_name, spec.Unchecked.short_name) with
  | None, None ->
      Error `No_name
  | Some ln, None ->
      Ok OptName.{ canonical = "--" ^ ln; aliases = [] }
  | None, Some sn ->
      Ok OptName.{ canonical = "-" ^ String.make 1 sn; aliases = [] }
  | Some ln, Some sn ->
      Ok
        OptName.
          { canonical = "--" ^ ln; aliases = [ "-" ^ String.make 1 sn ] } )
  |> Result.map (fun name ->
         Checked.
           { name
           ; meta_vars =
               Option.value ~default:[ "args" ] spec.Unchecked.meta_vars
           ; help_msg = spec.Unchecked.help_msg
           ; default_argument = spec.Unchecked.default_argument
           ; optional = spec.Unchecked.optional
           } )
