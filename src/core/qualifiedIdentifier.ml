open Support

type t =
  { location : Location.t
  ; modules : Identifier.t List.t
        (** The qualified identifier's modules in order of appeareance as in
            the external syntax. *)
  ; name : Identifier.t
  }

type qualified_identifier = t

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

include (
  (val Ord.sequence
         (module List.MakeOrd (Identifier))
         (module Identifier)
         modules name) :
    Ord.ORD with type t := t)

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
      | [] -> Format.fprintf ppf "%a" Identifier.pp (name n)
      | _ ->
        Format.fprintf ppf "%a::%a"
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "::")
             (fun ppf x -> Format.fprintf ppf "%a" Identifier.pp x))
          (modules n) Identifier.pp (name n)
  end) :
    Show.SHOW with type t := t)

module Dictionary = struct
  type 'a t = 'a value Identifier.Hamt.t

  and 'a value =
    | Entry of 'a
    | Module of 'a t

  let empty = Identifier.Hamt.empty

  let add_toplevel_entry identifier entry dictionary =
    Identifier.Hamt.add identifier (Entry entry) dictionary

  let add_nested qualified_identifier entry dictionary =
    let identifier = name qualified_identifier
    and modules = modules qualified_identifier in
    match modules with
    | [] (* Toplevel declaration *) ->
      Identifier.Hamt.add identifier entry dictionary
    | m :: ms (* Nested declaration *) ->
      let rec add_lookup module_to_lookup next_modules dictionary =
        let nested_dictionary =
          match Identifier.Hamt.find_opt module_to_lookup dictionary with
          | Option.Some (Module nested_dictionary)
          (* Addition to existing module *) -> nested_dictionary
          | Option.Some (Entry _) (* Entry shadowing *)
          | Option.None (* Module introduction *) -> empty
        in
        let nested_dictionary' =
          match next_modules with
          | [] (* Finished lookups *) ->
            Identifier.Hamt.add identifier entry nested_dictionary
          | m :: ms (* Recursively lookup next module *) ->
            add_lookup m ms nested_dictionary
        in
        Identifier.Hamt.add module_to_lookup (Module nested_dictionary')
          dictionary
      in
      add_lookup m ms dictionary

  let add_entry qualified_identifier entry dictionary =
    add_nested qualified_identifier (Entry entry) dictionary

  let add_module qualified_identifier sub_dictionary dictionary =
    add_nested qualified_identifier (Module sub_dictionary) dictionary

  exception Unbound_identifier of qualified_identifier

  exception Unbound_module of qualified_identifier

  exception Expected_module of qualified_identifier

  let pp_exception ppf = function
    | Unbound_identifier identifier ->
      Format.fprintf ppf "Identifier \"%a\" is unbound: %a" pp identifier
        Location.pp (location identifier)
    | Unbound_module identifier ->
      Format.fprintf ppf "Module \"%a\" is unbound: %a" pp identifier
        Location.pp (location identifier)
    | Expected_module identifier ->
      Format.fprintf ppf "Expected \"%a\" to be a module: %a@." pp identifier
        Location.pp (location identifier)
    | _ -> raise @@ Invalid_argument "[pp_exception] unsupported exception"

  let () =
    Printexc.register_printer (fun exn ->
        try Option.some @@ Format.stringify pp_exception exn
        with Invalid_argument _ -> Option.none)

  let lookup query dictionary =
    let rec lookup modules_to_lookup modules_looked_up_so_far dictionary =
      match modules_to_lookup with
      | [] (* Toplevel declaration *) -> (
        let name = name query in
        match Identifier.Hamt.find_opt name dictionary with
        | Option.Some entry -> entry
        | Option.None -> raise @@ Unbound_identifier query)
      | m :: ms (* Nested declaration *) -> (
        let recover_current_module_identifier () =
          make ~modules:(List.rev modules_looked_up_so_far) m
        in
        match Identifier.Hamt.find_opt m dictionary with
        | Option.Some (Module dictionary') ->
          lookup ms (m :: modules_looked_up_so_far) dictionary'
        | Option.Some (Entry _) ->
          raise @@ Expected_module (recover_current_module_identifier ())
        | Option.None ->
          raise @@ Unbound_module (recover_current_module_identifier ()))
    in
    let modules = modules query in
    lookup modules [] dictionary

  let toplevel_bindings = Fun.id

  let rec to_seq dictionary =
    dictionary |> Identifier.Hamt.bindings |> List.to_seq
    |> Seq.flat_map (function
         | identifier, (Module nested_dictionary as value) ->
           nested_dictionary |> to_seq
           |> Seq.map (fun (nested_entry_identifier, entry) ->
                  let identifier =
                    prepend_module identifier nested_entry_identifier
                  in
                  (identifier, entry))
           |> Seq.cons (make_simple identifier, value)
         | identifier, (Entry _ as value) ->
           let identifier = make_simple identifier in
           Seq.return (identifier, value))
end
