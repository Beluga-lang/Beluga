(** A module for functions to give information for an option. For example,
    functions that configure

    - the name of an option
    - the help message of an option
    - the fallback value of an optional option
    - etc. are included.

    @author Clare Jang *)

(** Unchecked options operations.

    @author Clare Jang *)
module Unchecked = struct
  type 'a t =
    { long_name : string option
    ; short_name : char option
    ; other_names : string list option
    ; meta_variables : string list option
    ; help_message : string option
    ; default_argument : 'a option
    ; optional : 'a option
    }

  type 'a transform = 'a t -> 'a t

  let empty =
    { long_name = None
    ; short_name = None
    ; other_names = None
    ; meta_variables = None
    ; help_message = None
    ; default_argument = None
    ; optional = None
    }


  let long_name ln spec = { spec with long_name = Some ln }

  let short_name sn spec = { spec with short_name = Some sn }

  let other_names ns spec = { spec with other_names = Some ns }

  let help_message hm spec = { spec with help_message = Some hm }

  let default_argument dv spec = { spec with default_argument = Some dv }

  let erase_default_argument spec = { spec with default_argument = None }

  let meta_variables mvs spec = { spec with meta_variables = Some mvs }

  let optional op spec = { spec with optional = Some op }

  let make transforms = transforms |> List.fold_left ( |> ) empty
end

module Checked = struct
  type 'a t =
    { name : OptName.t
    ; meta_variables : string list
    ; help_message : string option
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
      Ok { OptName.canonical = "--" ^ ln; aliases = [] }
  | None, Some sn ->
      Ok { OptName.canonical = "-" ^ String.make 1 sn; aliases = [] }
  | Some ln, Some sn ->
      Ok
        { OptName.canonical = "--" ^ ln
        ; aliases = [ "-" ^ String.make 1 sn ]
        } )
  |> Result.map (fun name ->
         { Checked.name
         ; meta_variables =
             Option.value ~default:[ "args" ] spec.Unchecked.meta_variables
         ; help_message = spec.Unchecked.help_message
         ; default_argument = spec.Unchecked.default_argument
         ; optional = spec.Unchecked.optional
         } )
