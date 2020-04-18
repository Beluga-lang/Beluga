open Support.Module

type t = int

let of_int x = x

module Make (_ : UNIT) = struct
  let counter = ref 0
  let next () =
    let x = !counter in
    incr counter;
    x
end

let string_of_hole_id = string_of_int

type name =
  | Anonymous
  | Named of string

let is_anonymous =
  function
  | Anonymous -> true
  | _ -> false

let name_of_option : string option -> name =
  function
  | Some name -> Named name
  | None -> Anonymous

let option_of_name : name -> string option =
  function
  | Anonymous -> None
  | Named s -> Some s

let string_of_name : name -> string =
  function
  | Anonymous -> ""
  | Named s -> s

let string_of_name_or_id : name * t -> string =
  function
  | Anonymous, i -> string_of_hole_id i
  | Named s, _ -> s

let fmt_ppr_name ppf : name -> unit =
  let open Format in
  function
  | Anonymous -> fprintf ppf "<anonymous>"
  | Named s -> fprintf ppf "?%s" s

let fmt_ppr_id ppf (id : t) =
  Format.fprintf ppf "%d" id

let compare = compare
