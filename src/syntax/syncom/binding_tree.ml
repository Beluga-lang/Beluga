open Support

exception Unbound_identifier = Identifier.Unbound_identifier

exception
  Unbound_qualified_identifier = Qualified_identifier
                                 .Unbound_qualified_identifier

exception Unbound_namespace = Qualified_identifier.Unbound_namespace

type 'a node =
  { entry : 'a
  ; subtree : 'a t
  }

and 'a t = 'a node Identifier.Hashtbl.t

let create () = Identifier.Hashtbl.create 0

let is_empty tree = Identifier.Hashtbl.length tree = 0

let[@inline] [@specialise] with_namespaces_and_identifier
    qualified_identifier f =
  let namespaces = Qualified_identifier.namespaces qualified_identifier in
  let identifier = Qualified_identifier.name qualified_identifier in
  f namespaces identifier

let[@inline] add_toplevel identifier entry ?(subtree = create ()) tree =
  Identifier.Hashtbl.add tree identifier { entry; subtree }

let rec add_nested namespaces identifier node tree =
  match namespaces with
  | [] -> Identifier.Hashtbl.add tree identifier node
  | n :: ns -> (
      match Identifier.Hashtbl.find_opt tree n with
      | Option.None ->
          Error.raise_notrace
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some { subtree; _ } -> (
          try add_nested ns identifier node subtree with
          | Unbound_namespace ns ->
              Error.raise_notrace
                (Unbound_namespace (Qualified_identifier.prepend_module n ns))
          ))

let add qualified_identifier entry ?(subtree = create ()) tree =
  with_namespaces_and_identifier qualified_identifier
    (fun namespaces identifier ->
      add_nested namespaces identifier { entry; subtree } tree)

let add_all t1 t2 =
  Identifier.Hashtbl.iter
    (fun identifier entry -> Identifier.Hashtbl.add t1 identifier entry)
    t2

let remove identifier tree =
  match Identifier.Hashtbl.find_opt tree identifier with
  | Option.None -> Error.raise_notrace (Unbound_identifier identifier)
  | Option.Some _ -> Identifier.Hashtbl.remove tree identifier

let lookup_toplevel identifier tree =
  match Identifier.Hashtbl.find_opt tree identifier with
  | Option.None -> Error.raise_notrace (Unbound_identifier identifier)
  | Option.Some { entry; subtree } -> (entry, subtree)

let lookup_toplevel_opt identifier tree =
  match Identifier.Hashtbl.find_opt tree identifier with
  | Option.None -> Option.none
  | Option.Some { entry; subtree } -> Option.some (entry, subtree)

let rec lookup_nested namespaces identifier tree =
  match namespaces with
  | [] -> (
      match Identifier.Hashtbl.find_opt tree identifier with
      | Option.None -> Error.raise_notrace (Unbound_identifier identifier)
      | Option.Some { entry; subtree } -> (entry, subtree))
  | n :: ns -> (
      match Identifier.Hashtbl.find_opt tree n with
      | Option.None ->
          Error.raise_notrace
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some { subtree; _ } -> (
          try lookup_nested ns identifier subtree with
          | Unbound_identifier identifier ->
              Error.raise_notrace
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n
                      (Qualified_identifier.make_simple identifier)))
          | Unbound_qualified_identifier identifier ->
              Error.raise_notrace
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n identifier))
          | Unbound_namespace ns ->
              Error.raise_notrace
                (Unbound_namespace (Qualified_identifier.prepend_module n ns))
          ))

let lookup qualified_identifier tree =
  with_namespaces_and_identifier qualified_identifier lookup_nested tree

let lookup_toplevel_filter identifier p tree =
  let value, subtree = lookup_toplevel identifier tree in
  if p value then (value, subtree)
  else Error.raise_notrace (Unbound_identifier identifier)

let lookup_toplevel_filter_opt identifier p tree =
  match lookup_toplevel_opt identifier tree with
  | Option.None -> Option.none
  | Option.Some (value, subtree) ->
      if p value then Option.some (value, subtree) else Option.none

let rec maximum_lookup identifiers tree =
  match identifiers with
  | List1.T (identifier, []) -> (
      match Identifier.Hashtbl.find_opt tree identifier with
      | Option.None -> `Unbound (List1.singleton identifier)
      | Option.Some { entry; subtree } -> `Bound (entry, subtree))
  | List1.T (x1, x2 :: xs) -> (
      match Identifier.Hashtbl.find_opt tree x1 with
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
      match Identifier.Hashtbl.find_opt tree identifier with
      | Option.None -> `Unbound (List1.singleton identifier)
      | Option.Some { entry; subtree } ->
          if p entry then `Bound (entry, subtree)
          else `Unbound (List1.singleton identifier))
  | List1.T (x1, x2 :: xs) -> (
      match Identifier.Hashtbl.find_opt tree x1 with
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
      match Identifier.Hashtbl.find_opt tree identifier with
      | Option.None -> false
      | Option.Some _node -> true)
  | n :: ns -> (
      match Identifier.Hashtbl.find_opt tree n with
      | Option.None -> false
      | Option.Some { subtree; _ } -> is_bound_nested ns identifier subtree)

let is_identifier_bound identifier tree = is_bound_nested [] identifier tree

let is_qualified_identifier_bound qualified_identifier tree =
  with_namespaces_and_identifier qualified_identifier is_bound_nested tree

let rec replace_nested namespaces identifier f tree =
  match namespaces with
  | [] -> (
      match Identifier.Hashtbl.find_opt tree identifier with
      | Option.None -> Error.raise_notrace (Unbound_identifier identifier)
      | Option.Some { entry; subtree } ->
          let entry', subtree' = f entry subtree in
          Identifier.Hashtbl.add tree identifier
            { entry = entry'; subtree = subtree' })
  | n :: ns -> (
      match Identifier.Hashtbl.find_opt tree n with
      | Option.None ->
          Error.raise_notrace
            (Unbound_namespace (Qualified_identifier.make_simple n))
      | Option.Some { subtree; _ } -> (
          try replace_nested ns identifier f subtree with
          | Unbound_identifier identifier ->
              Error.raise_notrace
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n
                      (Qualified_identifier.make_simple identifier)))
          | Unbound_qualified_identifier identifier ->
              Error.raise_notrace
                (Unbound_qualified_identifier
                   (Qualified_identifier.prepend_module n identifier))
          | Unbound_namespace ns ->
              Error.raise_notrace
                (Unbound_namespace (Qualified_identifier.prepend_module n ns))
          ))

let replace qualified_identifier f tree =
  with_namespaces_and_identifier qualified_identifier
    (fun namespaces identifier ->
      replace_nested namespaces identifier f tree)

let rec mem_nested namespaces identifier tree =
  match namespaces with
  | [] -> Identifier.Hashtbl.mem tree identifier
  | n :: ns -> (
      match Identifier.Hashtbl.find_opt tree n with
      | Option.None -> false
      | Option.Some { subtree; _ } -> mem_nested ns identifier subtree)

let mem qualified_identifier tree =
  with_namespaces_and_identifier qualified_identifier mem_nested tree

let rec snapshot tree =
  let tree' = Identifier.Hashtbl.create (Identifier.Hashtbl.length tree) in
  Identifier.Hashtbl.iter
    (fun key { entry; subtree } ->
      let subtree' = snapshot subtree in
      Identifier.Hashtbl.add tree' key { entry; subtree = subtree' })
    tree;
  tree'

let size =
  let rec size_tl tree acc =
    Identifier.Hashtbl.fold
      (fun _identifier { subtree; _ } acc -> size_tl subtree (acc + 1))
      tree acc
  in
  fun tree -> size_tl tree 0

let rec to_seq tree =
  Identifier.Hashtbl.fold
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
