open Support

type t =
  { location : Location.t
  ; name : Identifier.t
  ; modules : Identifier.t List.t
  }

let make ~location ?(modules = []) name = { location; name; modules }

let make_simple name =
  let location = Identifier.location name in
  make ~location name

let prepend_module module_name { location; name; modules } =
  let location = Location.join (Identifier.location module_name) location
  and modules = module_name :: modules in
  { location; modules; name }

let[@inline] location { location; _ } = location

let[@inline] name { name; _ } = name

let[@inline] modules { modules; _ } = modules

include (
  (val Ord.sequence
         (module Identifier)
         (module List.MakeOrd (Identifier))
         name modules) :
    Ord.ORD with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp ppf n =
      match modules n with
      | [] -> Format.fprintf ppf "%a" Identifier.pp (name n)
      | _ ->
        Format.fprintf ppf "%a::%a"
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "::")
             (fun ppf x -> Format.fprintf ppf "%a" Identifier.pp x))
          (modules n) Identifier.pp (name n)
  end) :
    Show.SHOW with type t := t)
