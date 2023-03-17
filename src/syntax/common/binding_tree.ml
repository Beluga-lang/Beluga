open Support

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Unbound_namespace of Qualified_identifier.t

type 'a node =
  { entry : 'a
  ; subtree : 'a tree
  }

and 'a tree = 'a node Identifier.Hamt.t

type 'a t = 'a tree

let empty = Identifier.Hamt.empty

let is_empty = Identifier.Hamt.is_empty

let[@inline] add_toplevel identifier entry ?(subtree = empty) tree =
  Identifier.Hamt.add identifier { entry; subtree } tree

let[@inline] with_namespaces_and_identifier qualified_identifier f =
  let namespaces = Qualified_identifier.namespaces qualified_identifier in
  let identifier = Qualified_identifier.name qualified_identifier in
  f namespaces identifier

let rec add_nested namespaces identifier node tree =
  match namespaces with
  | [] -> Identifier.Hamt.add identifier node tree
  | n :: ns -> (
      match Identifier.Hamt.find_opt n tree with
      | Option.None ->
          Error.raise
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some ({ subtree; _ } as namespace) ->
          let subtree' =
            try add_nested ns identifier node subtree with
            | Unbound_namespace ns ->
                Error.raise
                  (Unbound_namespace
                     (Qualified_identifier.prepend_module n ns))
          in
          Identifier.Hamt.add n { namespace with subtree = subtree' } tree)

let add qualified_identifier entry ?(subtree = empty) tree =
  with_namespaces_and_identifier qualified_identifier
    (fun namespaces identifier ->
      add_nested namespaces identifier { entry; subtree } tree)

let add_all t1 t2 =
  (*=
    It may be more efficient to use the following:
    {[
      Identifier.Hamt.union (fun _identifier _e1 e2 -> Option.some e2) t1 t2
    ]}

    However, there is a bug in [Identifier.Hamt.union]:
    https://github.com/thizanne/ocaml-hamt/issues/41
  *)
  Identifier.Hamt.fold
    (fun identifier entry accumulator ->
      Identifier.Hamt.add identifier entry accumulator)
    t2 t1

let remove identifier tree =
  match Identifier.Hamt.find_opt identifier tree with
  | Option.None -> Error.raise (Unbound_identifier identifier)
  | Option.Some _ -> Identifier.Hamt.remove identifier tree

let lookup_toplevel identifier tree =
  match Identifier.Hamt.find_opt identifier tree with
  | Option.None -> Error.raise (Unbound_identifier identifier)
  | Option.Some { entry; subtree } -> (entry, subtree)

let rec lookup_nested namespaces identifier tree =
  match namespaces with
  | [] -> (
      match Identifier.Hamt.find_opt identifier tree with
      | Option.None -> Error.raise (Unbound_identifier identifier)
      | Option.Some { entry; subtree } -> (entry, subtree))
  | n :: ns -> (
      match Identifier.Hamt.find_opt n tree with
      | Option.None ->
          Error.raise
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some { subtree; _ } -> (
          try lookup_nested ns identifier subtree with
          | Unbound_identifier identifier ->
              Error.raise
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n
                      (Qualified_identifier.make_simple identifier)))
          | Unbound_qualified_identifier identifier ->
              Error.raise
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n identifier))
          | Unbound_namespace ns ->
              Error.raise
                (Unbound_namespace (Qualified_identifier.prepend_module n ns))
          ))

let lookup qualified_identifier tree =
  with_namespaces_and_identifier qualified_identifier lookup_nested tree

let lookup_toplevel_filter identifier p tree =
  let value, subtree = lookup_toplevel identifier tree in
  if p value then (value, subtree)
  else Error.raise (Unbound_identifier identifier)

let rec maximum_lookup identifiers tree =
  match identifiers with
  | List1.T (identifier, []) -> (
      match Identifier.Hamt.find_opt identifier tree with
      | Option.None -> `Unbound (List1.singleton identifier)
      | Option.Some { entry; subtree } -> `Bound (entry, subtree))
  | List1.T (x1, x2 :: xs) -> (
      match Identifier.Hamt.find_opt x1 tree with
      | Option.None -> `Unbound identifiers
      | Option.Some { entry; subtree } -> (
          match maximum_lookup (List1.from x2 xs) subtree with
          | `Bound result -> `Bound result
          | `Partially_bound (bound, result, unbound) ->
              `Partially_bound (x1 :: bound, result, unbound)
          | `Unbound unbound ->
              `Partially_bound ([], (x1, entry, subtree), unbound)))

let rec maximum_lookup_filter identifiers p tree =
  match identifiers with
  | List1.T (identifier, []) -> (
      match Identifier.Hamt.find_opt identifier tree with
      | Option.None -> `Unbound (List1.singleton identifier)
      | Option.Some { entry; subtree } ->
          if p entry then `Bound (entry, subtree)
          else `Unbound (List1.singleton identifier))
  | List1.T (x1, x2 :: xs) -> (
      match Identifier.Hamt.find_opt x1 tree with
      | Option.None -> `Unbound identifiers
      | Option.Some { entry; subtree } ->
          if p entry then
            match maximum_lookup_filter (List1.from x2 xs) p subtree with
            | `Bound result -> `Bound result
            | `Partially_bound (bound, result, unbound) ->
                `Partially_bound (x1 :: bound, result, unbound)
            | `Unbound unbound ->
                `Partially_bound ([], (x1, entry, subtree), unbound)
          else `Unbound identifiers)

let open_namespace qualified_identifier tree =
  let _entry, subtree = lookup qualified_identifier tree in
  add_all tree subtree

let rec is_bound_nested namespaces identifier tree =
  match namespaces with
  | [] -> (
      match Identifier.Hamt.find_opt identifier tree with
      | Option.None -> false
      | Option.Some _node -> true)
  | n :: ns -> (
      match Identifier.Hamt.find_opt n tree with
      | Option.None -> false
      | Option.Some { subtree; _ } -> is_bound_nested ns identifier subtree)

let is_identifier_bound identifier tree = is_bound_nested [] identifier tree

let is_qualified_identifier_bound qualified_identifier tree =
  with_namespaces_and_identifier qualified_identifier is_bound_nested tree

let rec replace_nested namespaces identifier f tree =
  match namespaces with
  | [] -> (
      match Identifier.Hamt.find_opt identifier tree with
      | Option.None -> Error.raise (Unbound_identifier identifier)
      | Option.Some { entry; subtree } ->
          let entry', subtree' = f entry subtree in
          Identifier.Hamt.add identifier
            { entry = entry'; subtree = subtree' }
            tree)
  | n :: ns -> (
      match Identifier.Hamt.find_opt n tree with
      | Option.None ->
          Error.raise
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some ({ subtree; _ } as node) -> (
          try
            let subtree' = replace_nested ns identifier f subtree in
            Identifier.Hamt.add n { node with subtree = subtree' } tree
          with
          | Unbound_identifier identifier ->
              Error.raise
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n
                      (Qualified_identifier.make_simple identifier)))
          | Unbound_qualified_identifier identifier ->
              Error.raise
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n identifier))
          | Unbound_namespace ns ->
              Error.raise
                (Unbound_namespace (Qualified_identifier.prepend_module n ns))
          ))

let replace qualified_identifier f tree =
  with_namespaces_and_identifier qualified_identifier
    (fun namespaces identifier ->
      replace_nested namespaces identifier f tree)

let size =
  let rec size_tl tree acc =
    Identifier.Hamt.fold
      (fun _identifier { subtree; _ } acc -> size_tl subtree (acc + 1))
      tree acc
  in
  fun tree -> size_tl tree 0

let rec to_seq tree =
  Identifier.Hamt.fold
    (fun identifier { entry; subtree } acc ->
      let binding = (Qualified_identifier.make_simple identifier, entry) in
      let subtree_bindings =
        Seq.map
          (fun (nested_identifier, nested_entry) ->
            ( Qualified_identifier.prepend_module identifier nested_identifier
            , nested_entry ))
          (to_seq subtree)
      in
      Seq.cons binding (Seq.append subtree_bindings acc))
    tree Seq.empty

let () =
  Error.register_exception_printer (function
    | Unbound_identifier identifier ->
        Format.dprintf "Identifier %a is unbound." Identifier.pp identifier
    | Unbound_qualified_identifier qualified_identifier ->
        Format.dprintf "Identifier %a is unbound." Qualified_identifier.pp
          qualified_identifier
    | Unbound_namespace qualified_identifier ->
        Format.dprintf "Unbound namespace %a." Qualified_identifier.pp
          qualified_identifier
    | exn -> Error.raise_unsupported_exception_printing exn)
