(** Map data structure from namespaced identifiers to values. *)

exception Unbound_identifier of Identifier.t

exception Unbound_qualified_identifier of Qualified_identifier.t

exception Unbound_namespace of Qualified_identifier.t

(** The type of binding trees. *)
type 'a t

(** The empty binding tree. *)
val empty : 'a t

(** [is_empty tree] is [true] if and only if there are no bindings in [tree]. *)
val is_empty : 'a t -> bool

(** [add_toplevel identifier value ?subtree tree] is the binding tree derived
    from [tree] with the addition of [(value, subtree)] bound for
    [identifier], where [subtree] defaults to [empty]. This shadows any
    previous bindings for [identifier] in [tree]. *)
val add_toplevel : Identifier.t -> 'a -> ?subtree:'a t -> 'a t -> 'a t

val add : Qualified_identifier.t -> 'a -> ?subtree:'a t -> 'a t -> 'a t

(** [add_all t1 t2] is the binding tree derived from [t1] by adding all the
    bindings from [t2]. *)
val add_all : 'a t -> 'a t -> 'a t

(** [remove identifier tree] is the tree derived from [tree] where the
    binding for [identifier] is removed.

    @raise Unbound_identifier *)
val remove : Identifier.t -> 'a t -> 'a t

(** [lookup_toplevel identifier tree] is [(value, subtree)] where [value] and
    [subtree] are as added with {!add}.

    @raise Unbound_identifier *)
val lookup_toplevel : Identifier.t -> 'a t -> 'a * 'a t

(** [lookup qualified_identifier tree] is [(value, subtree)] where [value]
    and [subtree] are as added with {!add}.

    @raise Unbound_identifier
    @raise Unbound_qualified_identifier
    @raise Unbound_namespace *)
val lookup : Qualified_identifier.t -> 'a t -> 'a * 'a t

(** [open_namespace qualified_identifier tree] is the binding tree derived
    from [tree] by adding all the bindings from [subtree] if
    [lookup qualified_identifier tree = (_value, subtree)].

    @raise Unbound_identifier
    @raise Unbound_qualified_identifier
    @raise Unbound_namespace *)
val open_namespace : Qualified_identifier.t -> 'a t -> 'a t

(** [is_identifier_bound identifier tree] is [true] if and only if there is a
    binding for [identifier] in [tree]. *)
val is_identifier_bound : Identifier.t -> 'a t -> bool

(** [is_qualified_identifier_bound identifier tree] is [true] if and only if
    there is a binding for [identifier] in [tree]. *)
val is_qualified_identifier_bound : Qualified_identifier.t -> 'a t -> bool

(** [replace identifier f tree] is the tree derived from [tree] where the
    value bound at [identifier] is [f entry subtree], with [(entry, subtree)]
    being the result of [lookup identifier tree]. *)
val replace :
  Qualified_identifier.t -> ('a -> 'a t -> 'a * 'a t) -> 'a t -> 'a t

(** [size tree] is the total number of key-value pairs in [tree]. *)
val size : 'a t -> int

(** [to_seq tree] is the sequence of values mapped by qualified identifier in
    [tree]. *)
val to_seq : 'a t -> (Qualified_identifier.t * 'a) Seq.t
