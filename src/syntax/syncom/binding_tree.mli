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

val lookup_toplevel_opt : Identifier.t -> 'a t -> ('a * 'a t) Option.t

(** [lookup qualified_identifier tree] is [(value, subtree)] where [value]
    and [subtree] are as added with {!add}.

    @raise Unbound_identifier
    @raise Unbound_qualified_identifier
    @raise Unbound_namespace *)
val lookup : Qualified_identifier.t -> 'a t -> 'a * 'a t

(** [lookup_toplevel_filter identifier p tree] is
    [lookup_toplevel identifier tree = (value, subtree)] if [p value]. That
    is, the predicate [p] decides whether [identifier] should be unbound in
    [tree] after performing the lookup.

    This is useful because lookups performed in computation-level patterns
    discard all variable bindings in the outer scope.

    @raise Unbound_identifier
      if [lookup_toplevel identifier tree] raises it, or if [value] does not
      satisfy [p]. *)
val lookup_toplevel_filter :
  Identifier.t -> ('a -> Bool.t) -> 'a t -> 'a * 'a t

val lookup_toplevel_filter_opt :
  Identifier.t -> ('a -> Bool.t) -> 'a t -> ('a * 'a t) Option.t

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
val maximum_lookup :
     Identifier.t List1.t
  -> 'a t
  -> [ `Unbound of Identifier.t List1.t
     | `Partially_bound of
       Identifier.t List.t
       * (Identifier.t * 'a * 'a t)
       * Identifier.t List1.t
     | `Bound of 'a * 'a t
     ]

(** [maximum_lookup_filter identifier p tree] is the analog of
    {!lookup_toplevel_filter} for {!maximum_lookup}. *)
val maximum_lookup_filter :
     Identifier.t List1.t
  -> ('a -> Bool.t)
  -> 'a t
  -> [ `Unbound of Identifier.t List1.t
     | `Partially_bound of
       Identifier.t List.t
       * (Identifier.t * 'a * 'a t)
       * Identifier.t List1.t
     | `Bound of 'a * 'a t
     ]

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

val mem : Qualified_identifier.t -> 'a t -> Bool.t

(** [size tree] is the total number of key-value pairs in [tree]. *)
val size : 'a t -> Int.t

(** [to_seq tree] is the sequence of values mapped by qualified identifier in
    [tree]. *)
val to_seq : 'a t -> (Qualified_identifier.t * 'a) Seq.t

(** [create ()] is a new empty binding tree. *)
val create : Unit.t -> 'a t
