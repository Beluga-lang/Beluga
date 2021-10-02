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

let make_empty () : 'a unchecked =
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
let long_name ln : 'a unchecked = { (make_empty ()) with long_name = Some ln }

(**
   A function configures the option name that comprises a single character.
   In command line interface, it will be prepended by ["-"].
   For example, with the input parameter ['s'], the real CLI option name will be [-s]
   @author Clare Jang
 *)
let short_name sn : 'a unchecked = { (make_empty ()) with short_name = Some sn }

(**
   A function configures the option name that does not start with ["-"] or ["--"].
   In command line interface, it will be used as-is,
   so a user must specify an exact option name used in CLI.
   @author Clare Jang
 *)
let other_names ns : 'a unchecked = { (make_empty ()) with other_names = Some ns }

(**
   A function configures the help message for the option.
   @author Clare Jang
 *)
let help_msg hm : 'a unchecked = { (make_empty ()) with help_msg = Some hm }

(**
   A function configures the default argument of the option.
   The default argument is an argument used when the option accepts an argument but
   none is passed.
   This function makes only the argument of the option optional.
   To make the option itself, see {!optional}.
   @author Clare Jang
 *)
let default_argument (dv : 'a) : 'a unchecked = { (make_empty ()) with default_argument = Some dv }

(**
   A function configures the names of arguments in the help message for the option.
   Default meta name is ["args"].
   For example, if [--file] option takes one argument, default help message for that option
   starts with [  --file args   ...]. If you want to display [PATH] or [TARGET_FILE] instead of [args],
   pass that name to this function.
   @author Clare Jang
 *)
let meta_vars mvs : 'a unchecked = { (make_empty ()) with meta_vars = Some mvs }

(**
   A function configures whether the option is mandatory or not.
   A value provided to this function is the default value used when a user
   does not pass the option.
   To make the argument of the option optional instead of the option itself,
   see {!default_argument}.
   @author Clare Jang
 *)
let optional op : 'a unchecked = { (make_empty ()) with optional = Some op }

(**
   An internal function used in {!OptSpec} module.
   @author Clare Jang
 *)
let lift (spec : unit unchecked) : 'a unchecked =
  { long_name = spec.long_name
  ; short_name = spec.short_name
  ; other_names = spec.other_names
  ; meta_vars = spec.meta_vars
  ; help_msg = spec.help_msg
  ; default_argument = None
  ; optional = None
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
let merge (specs : 'a unchecked list) : 'a unchecked =
  let combine (spec0 : 'a unchecked) (spec1 : 'a unchecked) : 'a unchecked =
    let open Option in
    { long_name = fold ~none:spec1.long_name ~some spec0.long_name
    ; short_name = fold ~none:spec1.short_name ~some spec0.short_name
    ; other_names = fold ~none:spec1.other_names ~some spec0.other_names
    ; meta_vars = fold ~none:spec1.meta_vars ~some spec0.meta_vars
    ; help_msg = fold ~none:spec1.help_msg ~some spec0.help_msg
    ; default_argument = fold ~none:spec1.default_argument ~some spec0.default_argument
    ; optional = fold ~none:spec1.optional ~some spec0.optional
    }
  in
  List.fold_left combine (make_empty ()) specs

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
  let name_result =
    let open OptName in
    match spec.long_name, spec.short_name with
    | None, None -> Error NoName
    | Some ln, None -> Ok (Names ("--" ^ ln, []))
    | None, Some sn -> Ok (Names ("-" ^ String.make 1 sn, []))
    | Some ln, Some sn -> Ok (Names ("--" ^ ln, ["-" ^ String.make 1 sn]))
  in
  match name_result with
  | Error e -> Error e
  | Ok name ->
     Ok
       { name
       ; meta_vars = Option.fold ~none:["args"] ~some:Fun.id spec.meta_vars
       ; help_msg = spec.help_msg
       ; default_argument = spec.default_argument
       ; optional = spec.optional
       }
