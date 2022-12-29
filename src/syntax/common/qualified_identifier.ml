open Support

type t =
  { location : Location.t
  ; modules : Identifier.t List.t
        (** The qualified identifier's modules in order of appeareance as in
            the external syntax. *)
  ; name : Identifier.t
  }

let make ?location ?(modules = []) name =
  match (location, modules) with
  | Option.Some location, modules -> { location; modules; name }
  | Option.None, [] ->
      let location = Identifier.location name in
      { location; name; modules }
  | Option.None, modules ->
      (* Join all locations *)
      let location =
        List.fold_left
          (fun acc i -> Location.join acc (Identifier.location i))
          (Identifier.location name)
          modules
      in
      { location; modules; name }

let make_simple name =
  let location = Identifier.location name in
  { location; modules = []; name }

let prepend_module module_name { location; modules; name } =
  let location = Location.join (Identifier.location module_name) location
  and modules = module_name :: modules in
  { location; modules; name }

let[@inline] location { location; _ } = location

let[@inline] modules { modules; _ } = modules

let[@inline] name { name; _ } = name

module type ORD = Ord.ORD

module Ord =
  (val Ord.sequence
         (module List.MakeOrd (Identifier))
         (module Identifier)
         modules name)

include (Ord : ORD with type t := t)

include (
  (val Eq.conjunction
         (module Identifier)
         (module List.MakeEq (Identifier))
         name modules) :
    Eq.EQ with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp ppf n =
      match modules n with
      | [] -> Identifier.pp ppf (name n)
      | _ ->
          Format.fprintf ppf "@[<2>%a@,.%a@]"
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,.")
               Identifier.pp)
            (modules n) Identifier.pp (name n)
  end) :
    Show.SHOW with type t := t)

module Map = Map.Make (Ord)
module Set = Set.Make (Ord)
