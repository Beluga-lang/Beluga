open Support

type t =
  { location : Location.t
  ; namespaces : Identifier.t List.t
        (** The qualified identifier's namespaces in order of appeareance as
            in the external syntax. *)
  ; name : Identifier.t
  }

let make ?location ?(namespaces = []) name =
  match (location, namespaces) with
  | Option.Some location, namespaces -> { location; namespaces; name }
  | Option.None, [] ->
      let location = Identifier.location name in
      { location; name; namespaces }
  | Option.None, namespaces ->
      (* Join all locations *)
      let location =
        List.fold_left
          (fun acc i -> Location.join acc (Identifier.location i))
          (Identifier.location name)
          namespaces
      in
      { location; namespaces; name }

let make_simple name =
  let location = Identifier.location name in
  { location; namespaces = []; name }

let prepend_module module_name { location; namespaces; name } =
  let location = Location.join (Identifier.location module_name) location
  and namespaces = module_name :: namespaces in
  { location; namespaces; name }

let[@inline] location { location; _ } = location

let[@inline] namespaces { namespaces; _ } = namespaces

let[@inline] name { name; _ } = name

let from_list1 identifiers =
  let namespaces, name = List1.unsnoc identifiers in
  make ~namespaces name

let to_list1 identifier =
  List1.append_list identifier.namespaces (List1.singleton identifier.name)

module type ORD = Ord.ORD

module Ord =
  (val Ord.sequence
         (module List.MakeOrd (Identifier))
         (module Identifier)
         namespaces name)

include (Ord : ORD with type t := t)

include (
  (val Eq.conjunction
         (module Identifier)
         (module List.MakeEq (Identifier))
         name namespaces) :
    Eq.EQ with type t := t)

include (
  Show.Make (struct
    type nonrec t = t

    let pp ppf n =
      match namespaces n with
      | [] -> Identifier.pp ppf (name n)
      | _ ->
          Format.fprintf ppf "@[<hov 2>%a@,.%a@]"
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,.")
               Identifier.pp)
            (namespaces n) Identifier.pp (name n)
  end) :
    Show.SHOW with type t := t)

module Map = Map.Make (Ord)
module Set = Set.Make (Ord)
