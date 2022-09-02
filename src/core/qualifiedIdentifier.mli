(** Namespaced identifiers.

    These are names for referring to bound variable names nested in modules. *)

open Support

type t

type qualified_identifier = t

(** {1 Constructors} *)

(** [make ?location ?modules name] is the qualified identifier having
    location [location], modules [modules] and name [name]. The modules in
    [modules] are expcted to be in order of appeareance as in the external
    syntax.

    - If [location] is unspecified and [modules = \[\]], then the location is
      that of [name].
    - If [location] is unspecified and [modules <> \[\]], then the location
      is the union of the locations for each module in [modules] and the
      location of [name]. *)
val make :
  ?location:Location.t -> ?modules:Identifier.t List.t -> Identifier.t -> t

(** [make_simple name] is [make name]. *)
val make_simple : Identifier.t -> t

(** [prepend_module module_ qid] is the qualified name derived from [qid]
    with [module_] prepended to it. *)
val prepend_module : Identifier.t -> t -> t

(** {1 Destructors} *)

val location : t -> Location.t

val modules : t -> Identifier.t List.t

val name : t -> Identifier.t

(** {1 Instances} *)

(** Equality of qualified identifiers by modules and names. Locations are
    ignored. *)
include Eq.EQ with type t := t

(** Lexicographical ordering of qualified identifiers. *)
include Ord.ORD with type t := t

include Show.SHOW with type t := t

(** {1 Collections} *)

(** A dictionary is a hash array mapped trie (HAMT) where keys are qualified
    identifiers and values are arranged in modules.

    Adding an entry to a dictionary shadows the previous binding of the same
    qualified identifier.

    For instance, consider the following dictionary:

    {[
      EntryA -> A
      Module::EntryB -> B
      Module::EntryC -> C
    ]}
    - If [(EntryA, D)] is added, then the binding [(EntryA, A)] is discarded.
    - If [(Module::EntryB, E)] is added, then the binding
      [(Module::EntryB, B)] is discarded.
    - If [(Module, F)] is added, then the bindings [(Module::EntryB, B)] and
      [(Module::EntryC, C)] are discarded.

    This dictionary data structure is persistent, and suited for keeping
    track of currently bound identifiers and bound qualified identifiers in
    the state monad. Modules are represented as sub-dictionaries for
    performance. *)
module Dictionary : sig
  (** ['a t] is the type of dictionaries whose entries range over ['a]. *)
  type 'a t

  (** ['a value] is the type of values mapped by qualified identifier in a
      dictionary. *)
  type 'a value = private
    | Entry of 'a
        (** [Entry a] is the value bound to a qualified identifier when added
            with {!add_entry}. *)
    | Module of 'a t
        (** [Module d] is the value bound to a qualified identifier when
            added with {!add_module}. *)

  (** {2 Constructors} *)

  (** [empty] is the empty dictionary. *)
  val empty : _ t

  (** [add_toplevel_entry identifier value dictionary] is the dictionary
      derived from [dictionary] with the added binding of [value] to
      [identifier].

      If the binding already exists in [dictionary], then it is replaced in
      the derived dictionary. *)
  val add_toplevel_entry : Identifier.t -> 'a -> 'a t -> 'a t

  (** [add_entry identifier value dictionary] is the dictionary derived from
      [dictionary] with the added binding of [value] to [identifier].

      If the binding already exists in [dictionary], then it is replaced in
      the derived dictionary. Additionally, modules in [identifier] are
      modules in the derived [dictionary], which may shadow other bindings.

      Note that [value] may not introduce other identifiers in the
      dictionary. That is, [value] should not represent a collection of
      values bound to identifiers. For adding modules, see {!add_module}. *)
  val add_entry : qualified_identifier -> 'a -> 'a t -> 'a t

  (** [add_module identifier sub_dictionary dictionary] is the dictionary
      derived from [dictionary] with the added binding of module
      [sub_dictionary] to [identifier].

      If the binding already exists in [dictionary], then it is replaced in
      the derived dictionary. Additionally, modules in [identifier] are
      modules in the derived [dictionary], which may shadow other bindings. *)
  val add_module : qualified_identifier -> 'a t -> 'a t -> 'a t

  (** {2 Lookup} *)

  (** [Unbound_identifier qid] is the exception raised when the identifier
      [qid] does not appear in a dictionary.

      This exception is raised, for instance, if [z] does not appear as a
      top-level entry in a dictionary, or if [Nat::z] does not appear as a
      nested entry in a dictionary (while [Nat] is a bound module). *)
  exception Unbound_identifier of qualified_identifier

  (** [Unbound_module qid] is the exception raised when an identifier's
      module at [qid] does not appear in a dictionary.

      This exception is raised, for instance, if the module [Nat] is unbound
      in a dictionary and [Nat::z] is looked up. *)
  exception Unbound_module of qualified_identifier

  (** [Expected_module qid] is the exception raised when an identifier's
      module at [qid] appears as an entry rather than a module in a
      dictionary.

      This exception is raised, for instance, if [Nat::z] is an entry in a
      dictionary, and [Nat::z::t] is looked up, since it was expected that
      [Nat::z] would be a module rather than an entry. *)
  exception Expected_module of qualified_identifier

  (** [lookup identifier dictionary] looks up [identifier] in [dictionary].

      @raise Unbound_identifier
      @raise Unbound_module
      @raise Expected_module *)
  val lookup : qualified_identifier -> 'a t -> 'a value

  (** [toplevel_bindings dictionary] is the HAMT of bindings globally in
      scope in [dictionary]. *)
  val toplevel_bindings : 'a t -> 'a value Identifier.Hamt.t

  (** {2 Interoperability} *)

  (** [to_seq dictionary] is [dictionary] flattened to a sequence of bindings
      by qualified name. There is no guarantee on the order of bindings in
      the resultant sequence. *)
  val to_seq : 'a t -> (qualified_identifier * 'a value) Seq.t
end
