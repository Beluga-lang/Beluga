(** Namespaced identifiers.

    These are names for referring to bound variable names nested in modules. *)

open Support

type t

type qualified_identifier = t

(** {1 Constructors} *)

val make :
  location:Location.t -> ?modules:Identifier.t List.t -> Identifier.t -> t

val make_simple : Identifier.t -> t

val prepend_module : Identifier.t -> t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val name : t -> Identifier.t

val modules : t -> Identifier.t List.t

(** {1 Instances} *)

include Eq.EQ with type t := t

include Ord.ORD with type t := t

include Show.SHOW with type t := t

(** {1 Collections} *)

(** A dictionary is a hash array mapped trie (HAMT) where keys are qualified
    identifiers and values are arranged in modules. This data structure is
    persistent, and suited for keeping track of currently bound identifiers
    and bound qualified identifiers in the state monad. Modules are
    represented as sub-dictionaries for performance. *)
module Dictionary : sig
  type 'a t

  type key = qualified_identifier

  type 'a value = private
    | Entry of 'a
    | Module of 'a t

  (** {2 Constructors} *)

  (** [empty] is the empty dictionary. *)
  val empty : _ t

  (** [add_entry identifier value dictionary] is the dictionary derived from
      [dictionary] with the added binding of [value] to [identifier]. If the
      binding already exists in [dictionary], then it is replaced in the
      derived dictionary. Additionally, modules in [identifier] are modules
      in the derived [dictionary], which may shadow other bindings.

      Note that [value] may not introduce other identifiers in the
      dictionary. That is, [value] should not represent a collection of
      values bound to identifiers. For adding modules, see {!add_module}. *)
  val add_entry : qualified_identifier -> 'a -> 'a t -> 'a t

  (** [add_module identifier sub_dictionary dictionary] is the dictionary
      derived from [dictionary] with the added binding of module
      [sub_dictionary] to [identifier]. If the binding already exists in
      [dictionary], then it is replaced in the derived dictionary.
      Additionally, modules in [identifier] are modules in the derived
      [dictionary], which may shadow other bindings. *)
  val add_module : qualified_identifier -> 'a t -> 'a t -> 'a t

  (** {2 Lookup} *)

  (** The type of exception raised when an identifier does not appear in a
      dictionary.

      For instance, if [z] does not appear as a top-level entry in a
      dictionary, or if [Nat::z] does not appear as a nested entry in a
      dictionary (while [Nat] is a bound module). *)
  exception Unbound_identifier of qualified_identifier

  (** The type of exception raised when an identifier's module does not
      appear in a dictionary.

      For instance, if the module [Nat] is unbound in a dictionary and
      [Nat::z] is looked up. *)
  exception Unbound_module of qualified_identifier

  (** The type of exception raised when an identifier's module appears as an
      entry rather than a module in a dictionary.

      For instance, if [Nat::z] is an entry in a dictionary, and [Nat::z::t]
      is looked up, it was expected that [Nat::z] would be a module rather
      than an entry. *)
  exception Expected_module of qualified_identifier

  (** [lookup identifier dictionary] looks up [identifier] in [dictionary].

      @raise Unbound_identifier
      @raise Unbound_module
      @raise Expected_module *)
  val lookup : qualified_identifier -> 'a t -> 'a value

  (** {2 Interoperability} *)

  (** [to_seq dictionary] is [dictionary] flattened to a sequence of bindings
      by qualified name. There is no guarantee on the order of bindings in
      the resultant sequence. *)
  val to_seq : 'a t -> (qualified_identifier * 'a value) Seq.t
end
