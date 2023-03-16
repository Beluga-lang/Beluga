open Support

type t = int

let of_int x = x

module Make () = struct
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

let is_anonymous = function
  | Anonymous -> true
  | Named _ -> false

let name_of_option : string option -> name = function
  | Option.Some name -> Named name
  | Option.None -> Anonymous

let option_of_name : name -> string option = function
  | Anonymous -> Option.none
  | Named s -> Option.some s

let string_of_name : name -> string = function
  | Anonymous -> ""
  | Named s -> s

let string_of_name_or_id : name * t -> string = function
  | Anonymous, i -> string_of_hole_id i
  | Named s, _ -> s

let fmt_ppr_name ppf : name -> unit = function
  | Anonymous -> Format.fprintf ppf "<anonymous>"
  | Named s -> Format.fprintf ppf "?%s" s

let fmt_ppr_id = Format.pp_print_int

let compare = compare
