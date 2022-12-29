(** Namespaced identifiers.

    These are names for referring to bound names nested in modules.

    Qualified identifiers may be prefixed by the modules that need to be
    opened in order to bring the referred constant in the current scope. The
    parts of a qualified identifier are delimited by ['.'].

    For instance, if [z] is an LF term-level constant, then the following are
    qualified identifiers:

    - [z]
    - [Nat.z]
    - [Util.Nat.z] *)

open Support

type t

(** {1 Constructors} *)

(** [make ?location ?modules name] is the qualified identifier having
    location [location], modules [modules] and name [name].

    The modules in [modules] are expected to be in order of appeareance as in
    the external syntax. That is, the qualified identifier [qid = Util.Nat.z]
    has [modules qid = \["Util"; "Nat"\]].

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

(** [location qid] is the location of [qid]. *)
val location : t -> Location.t

(** [modules qid] is the module prefixes of [qid].

    For instance, if [qid = Util.Nat.z], then
    [modules qid = \["Util"; "Nat"\]]. *)
val modules : t -> Identifier.t List.t

(** [name qid] is the identifier in the tail end position of [qid].

    For instance, if [qid = Util.Nat.z], then [name qid = "z"]. *)
val name : t -> Identifier.t

(** {1 Instances} *)

(** Equality of qualified identifiers by modules and names. Locations are
    ignored. *)
include Eq.EQ with type t := t

(** Lexicographical ordering of qualified identifiers. *)
include Ord.ORD with type t := t

include Show.SHOW with type t := t

(** {1 Collections} *)

module Map : Map.S with type key = t

module Set : Set.S with type elt = t
