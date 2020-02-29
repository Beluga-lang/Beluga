open Util

type 'a unchecked =
  { long_name : string option
  ; short_name : char option
  ; other_names : string list option
  ; meta_vars : string list option
  ; help_msg : string option
  ; default_argument : 'a option
  ; condition : ('a -> bool) option
  ; optional : 'a option
  }

let make_empty () : 'a unchecked =
  { long_name = None
  ; short_name = None
  ; other_names = None
  ; meta_vars = None
  ; help_msg = None
  ; default_argument = None
  ; condition = None
  ; optional = None
  }

let long_name ln : 'a unchecked = { (make_empty ()) with long_name = Some ln }
let short_name sn : 'a unchecked = { (make_empty ()) with short_name = Some sn }
let other_names ns : 'a unchecked = { (make_empty ()) with other_names = Some ns }
let help_msg hm : 'a unchecked = { (make_empty ()) with help_msg = Some hm }
let default_argument (dv : 'a) : 'a unchecked = { (make_empty ()) with default_argument = Some dv }
let condition cd : 'a unchecked = { (make_empty ()) with condition = Some cd }
let meta_vars mvs : 'a unchecked = { (make_empty ()) with meta_vars = Some mvs }
let optional op : 'a unchecked = { (make_empty ()) with optional = Some op }

let lift (spec : unit unchecked) : 'a unchecked =
  { long_name = spec.long_name
  ; short_name = spec.short_name
  ; other_names = spec.other_names
  ; meta_vars = spec.meta_vars
  ; help_msg = spec.help_msg
  ; default_argument = None
  ; condition = Option.map (fun f -> (fun _ -> f ())) spec.condition
  ; optional = None
  }

(* It's not possible to do eta-conversion.
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
    ; condition = fold ~none:spec1.condition ~some spec0.condition
    ; optional = fold ~none:spec1.optional ~some spec0.optional
    }
  in
  List.fold_left combine (make_empty ()) specs

type 'a checked =
  { name : OptName.t
  ; meta_vars : string list
  ; help_msg : string option
  ; default_argument : 'a option
  ; condition : ('a -> bool) option
  ; optional : 'a option
  }

type check_error =
  | NoName

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
       ; meta_vars = Option.fold ~none:["args"] ~some:id spec.meta_vars
       ; help_msg = spec.help_msg
       ; default_argument = spec.default_argument
       ; condition = spec.condition
       ; optional = spec.optional
       }
