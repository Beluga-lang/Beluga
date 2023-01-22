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
  Identifier.Hamt.union (fun _identifier _e1 e2 -> e2) t1 t2

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

let open_namespace qualified_identifier tree =
  let _entry, subtree = lookup qualified_identifier tree in
  add_all tree subtree

let is_identifier_bound identifier tree =
  match Identifier.Hamt.find_opt identifier tree with
  | Option.None -> false
  | Option.Some _node -> true

let pp_exception ppf = function
  | Unbound_identifier identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Identifier.pp identifier
  | Unbound_qualified_identifier qualified_identifier ->
      Format.fprintf ppf "Identifier %a is unbound." Qualified_identifier.pp
        qualified_identifier
  | Unbound_namespace qualified_identifier ->
      Format.fprintf ppf "Unbound namespace %a." Qualified_identifier.pp
        qualified_identifier
  | _ -> raise (Invalid_argument "[pp_exception] unsupported exception")

let () =
  Printexc.register_printer (fun exn ->
      try Option.some (Format.stringify pp_exception exn) with
      | Invalid_argument _ -> Option.none)
