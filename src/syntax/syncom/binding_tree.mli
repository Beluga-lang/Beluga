(** Mutable map data structure from namespaced identifiers to values.

    A binding tree is a tree of identifiers mapped to values, like in a map
    data structure. Entries in a binding tree are toplevel if they are direct
    children of the tree root (i.e., they are not entries nested in
    namespaces). Identifiers may be used as keys for toplevel entries in the
    tree, and qualified identifiers may be used as keys for all entries in
    the tree (toplevel or nested in namespaces). Hence, a lookup in a binding
    tree traverses the tree from the root to an internal node or leaf by
    sequentially traversing the list of identifier segments in the qualified
    identifier. *)

open Support

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Unbound_namespace of Qualified_identifier.t

(** The type of binding trees. *)
type 'a t

(** [is_empty tree] is [true] if and only if there are no bindings in [tree]. *)
val is_empty : 'a t -> Bool.t

(** [add_toplevel identifier value ?subtree tree] adds [(value, subtree)]
    bound for [identifier] in [tree], where [subtree] defaults to [empty].
    This shadows any previous bindings for [identifier] in [tree]. *)
val add_toplevel : Identifier.t -> 'a -> ?subtree:'a t -> 'a t -> Unit.t

(** [add identifier entry ?subtree tree] adds [entry] and [subtree] bound to
    [identifier] in [tree]. The namespaces of [identifier] must be bound in
    [tree].

    @raise Unbound_namespace *)
val add : Qualified_identifier.t -> 'a -> ?subtree:'a t -> 'a t -> Unit.t

(** [add_all t1 t2] adds all the bindings from [t2] to [t1]. *)
val add_all : 'a t -> 'a t -> Unit.t

(** [remove identifier tree] removes the binding in [tree] for [identifier].

    @raise Unbound_identifier *)
val remove : Identifier.t -> 'a t -> Unit.t

(** [lookup_toplevel identifier tree] is [(value, subtree)] where [value] and
    [subtree] are as added with {!add}.

    @raise Unbound_identifier *)
val lookup_toplevel : Identifier.t -> 'a t -> 'a * 'a t

(** [lookup_toplevel_opt identifier tree] is [Option.Some (value, subtree)]
    where [value] and [subtree] are as added with {!add}, and [Option.None]
    if there is no binding in [tree] for [identifier]. *)
val lookup_toplevel_opt : Identifier.t -> 'a t -> ('a * 'a t) Option.t

(** [lookup qualified_identifier tree] is [(value, subtree)] where [value]
    and [subtree] are as added with {!add}.

    @raise Unbound_identifier
    @raise Unbound_qualified_identifier
    @raise Unbound_namespace *)
val lookup : Qualified_identifier.t -> 'a t -> 'a * 'a t

type 'a maximum_lookup_result =
  | Unbound of { segments : Identifier.t List1.t }
  | Partially_bound of
      { leading_segments : Identifier.t List.t
      ; segment : Identifier.t
      ; trailing_segments : Identifier.t List1.t
      ; entry : 'a
      ; subtree : 'a t
      }
  | Bound of
      { entry : 'a
      ; subtree : 'a t
      }

(** [maximum_lookup identifiers tree] looks up as many bound identifiers in
    [identifiers] as possible against [tree] in sequence. This effectively
    matches [identifiers] as a path in [tree].

    [maximum_lookup identifiers tree] is one of three outcomes, in increasing
    length of matching path:

    + [`Unbound identifiers] if the first identifier in [identifiers] is not
      bound in [tree], so [identifiers] is not a path in [tree].
    + [`Partially_bound (bound, (entry, subtree), unbound_identifiers)] if
      not all identifiers in [identifiers] are bound in [tree], so first few
      identifiers form a path in [tree].
    + [`Bound (entry, subtree)] if all identifiers in [identifiers] are
      bound, so they form a path in [tree]. *)
val maximum_lookup : Identifier.t List1.t -> 'a t -> 'a maximum_lookup_result

(** [open_namespace qualified_identifier tree] adds all the bindings from
    [subtree] to [tree] if
    [lookup qualified_identifier tree = (_value, subtree)].

    @raise Unbound_identifier
    @raise Unbound_qualified_identifier
    @raise Unbound_namespace *)
val open_namespace : Qualified_identifier.t -> 'a t -> Unit.t

(** [is_identifier_bound identifier tree] is [true] if and only if there is a
    binding for [identifier] in [tree]. *)
val is_identifier_bound : Identifier.t -> 'a t -> Bool.t

(** [is_qualified_identifier_bound identifier tree] is [true] if and only if
    there is a binding for [identifier] in [tree]. *)
val is_qualified_identifier_bound : Qualified_identifier.t -> 'a t -> Bool.t

(** [replace identifier f tree] replaces the value bound at [identifier] in
    [tree] with [f entry subtree], with [(entry, subtree)] being the result
    of [lookup identifier tree]. *)
val replace :
  Qualified_identifier.t -> ('a -> 'a t -> 'a * 'a t) -> 'a t -> Unit.t

(** [mem identifier tree] is [true] if and only if there is a binding in
    [tree] for [identifier]. *)
val mem : Qualified_identifier.t -> 'a t -> Bool.t

(** [snapshot tree] is a duplicate of [tree] that only retains the latest
    bindings. The values are kept as is. Snapshots of the subtrees in [tree]
    are also taken. A snapshot is not a deep copy precisely because the old
    bindings in the hashtables are not carried over.

    A snapshot of a binding tree is essentially a frozen duplicate of it.
    This means that bindings in the snapshot cannot be removed in the same
    way that they are in the original tree because the previous bindings for
    any key are not copied over to the snapshot.

    This is used to produce snapshots of the referencing environment during a
    traversal of a Beluga signature at the point of declaration of Harpoon
    programs, so that we may revisit the referencing environment at those
    points later. *)
val snapshot : 'a t -> 'a t

(** [size tree] is the total number of key-value pairs in [tree]. *)
val size : 'a t -> Int.t

(** [to_seq tree] is the sequence of values mapped by qualified identifier in
    [tree]. *)
val to_seq : 'a t -> (Qualified_identifier.t * 'a) Seq.t

(** [create ()] is a new empty binding tree. *)
val create : Unit.t -> 'a t
