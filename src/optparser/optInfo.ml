(**
   A module for functions to give information for an option.
   For example, functions that configure
   - the name of an option
   - the help message of an option
   - the fallback value of an optional option
   - etc.
   are included.
   @author Clare Jang
 *)

(**
   A type built by a user using functions in this module.
   A value of this type will be merged and checked in the functions of {!OptSpec} module.
   @author Clare Jang
 *)
type 'a unchecked =
  { long_name : string option
  ; short_name : char option
  ; other_names : string list option
  ; meta_vars : string list option
  ; help_msg : string option
  ; default_argument : 'a option
  ; optional : 'a option
  }

let empty : 'a unchecked =
  { long_name = None
  ; short_name = None
  ; other_names = None
  ; meta_vars = None
  ; help_msg = None
  ; default_argument = None
  ; optional = None
  }

(**
   A function configures the option name that contains more than two characters.
   In command line interface, it will be prepended by ["--"].
   For example, with the input parameter ["abc"], the real CLI option name will be [--abc]
   @author Clare Jang
 *)
let long_name ln : 'a unchecked =
  { empty with long_name = Some ln }

(**
   A function configures the option name that comprises a single character.
   In command line interface, it will be prepended by ["-"].
   For example, with the input parameter ['s'], the real CLI option name will be [-s]
   @author Clare Jang
 *)
let short_name sn : 'a unchecked =
  { empty with short_name = Some sn }

(**
   A function configures the option name that does not start with ["-"] or ["--"].
   In command line interface, it will be used as-is,
   so a user must specify an exact option name used in CLI.
   @author Clare Jang
 *)
let other_names ns : 'a unchecked =
  { empty with other_names = Some ns }

(**
   A function configures the help message for the option.
   @author Clare Jang
 *)
let help_msg hm : 'a unchecked =
  { empty with help_msg = Some hm }

(**
   A function configures the default argument of the option.
   The default argument is an argument used when the option accepts an argument but
   none is passed.
   This function makes only the argument of the option optional.
   To make the option itself, see {!optional}.
   @author Clare Jang
 *)
let default_argument (dv : 'a) : 'a unchecked =
  { empty with default_argument = Some dv }

(**
   A function configures the names of arguments in the help message for the option.
   Default meta name is ["args"].
   For example, if [--file] option takes one argument, default help message for that option
   starts with [  --file args   ...]. If you want to display [PATH] or [TARGET_FILE] instead of [args],
   pass that name to this function.
   @author Clare Jang
 *)
let meta_vars mvs : 'a unchecked =
  { empty with meta_vars = Some mvs }

(**
   A function configures whether the option is mandatory or not.
   A value provided to this function is the default value used when a user
   does not pass the option.
   To make the argument of the option optional instead of the option itself,
   see {!default_argument}.
   @author Clare Jang
 *)
let optional op : 'a unchecked =
  { empty with optional = Some op }

(**
   An internal function used in {!OptSpec} module.
   @author Clare Jang
 *)
let lift (spec : unit unchecked) : 'a unchecked =
  { spec with default_argument = None ; optional = None }

let (<|>) (spec0 : 'a unchecked) (spec1 : 'a unchecked) : 'a unchecked =
  let open Option in
  { long_name = spec0.long_name <|> spec1.long_name
  ; short_name = spec0.short_name <|> spec1.short_name
  ; other_names = spec0.other_names <|> spec1.other_names
  ; meta_vars = spec0.meta_vars <|> spec1.meta_vars
  ; help_msg = spec0.help_msg <|> spec1.help_msg
  ; default_argument = spec0.default_argument <|> spec1.default_argument
  ; optional = spec0.optional <|> spec1.optional
  }

(**
   An internal function used in {!OptSpec} module.
   @author Clare Jang
 *)
(*
  It's not possible to do eta-conversion.
  By eta-conversion, it loses its polymorphicity,
  and fails to check against its signature
 *)
let merge: 'a unchecked list -> 'a unchecked =
  List.fold_left (<|>) empty

(**
   An internal type used in {!OptSpec} module.
   @author Clare Jang
 *)
type 'a checked =
  { name : OptName.t
  ; meta_vars : string list
  ; help_msg : string option
  ; default_argument : 'a option
  ; optional : 'a option
  }

(**
   An error type which might be emited from the functions in {!OptSpec} module.
   @author Clare Jang
 *)
type check_error =
  | NoName

(**
   An internal function used in {!OptSpec} module.
   @author Clare Jang
 *)
let check spec =
  ( let open OptName in
    match spec.long_name, spec.short_name with
    | None, None ->
        Error NoName

    | Some ln, None ->
        Ok { canonical = "--" ^ ln; aliases = [] }

    | None, Some sn ->
        Ok { canonical = "-" ^ String.make 1 sn; aliases = [] }

    | Some ln, Some sn ->
        Ok { canonical = "--" ^ ln; aliases = ["-" ^ String.make 1 sn] }
  )
  |> Result.map
  (fun name ->
    { name
    ; meta_vars = Option.value ~default:["args"] spec.meta_vars
    ; help_msg = spec.help_msg
    ; default_argument = spec.default_argument
    ; optional = spec.optional
    }
  )
