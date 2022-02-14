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

  let empty =
    { long_name = None
    ; short_name = None
    ; other_names = None
    ; meta_variables = None
    ; help_message = None
    ; default_argument = None
    ; optional = None
    }


  let long_name ln = { empty with long_name = Some ln }

  let short_name sn = { empty with short_name = Some sn }

  let other_names ns = { empty with other_names = Some ns }

  let help_message hm = { empty with help_message = Some hm }

  let default_argument dv = { empty with default_argument = Some dv }

  let meta_variables mvs = { empty with meta_variables = Some mvs }

  let optional op = { empty with optional = Some op }

  let lift spec = { spec with default_argument = None; optional = None }

  let merge spec0 spec1 =
    let open Option in
    { long_name = spec0.long_name <|> spec1.long_name
    ; short_name = spec0.short_name <|> spec1.short_name
    ; other_names = spec0.other_names <|> spec1.other_names
    ; meta_variables = spec0.meta_variables <|> spec1.meta_variables
    ; help_message = spec0.help_message <|> spec1.help_message
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
