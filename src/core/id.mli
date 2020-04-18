(** A `name' represents the original named representation of a
    variable.  These are primarily used in parsing and pretty-
    printing.  Names should never be constructed directly.
    See `mk_name'. *)
type name

(* For reporting whether a name is used in a context. *)
type max_usage =
  [ `used of int option
  | `unused
  ]

val base_name : name -> string
val get_module : name -> string list

(** Generate a blank name (underscore). *)
val mk_blank : Location.t option -> name

val inc_hint_cnt : int option -> int option
val gen_fresh_name : name list -> name -> name
val inc : name -> name

(** Retrieves the location of this identifier.
    For identifiers generated internally, this will be a ghost.
 *)
val loc_of_name : name -> Location.t

(** Finds the maximum number used for the given name hint in the given
    context.
    Returns None if the name hint is unused.
 *)
val max_usage : name list -> string -> max_usage

(** Change the number of a variable. *)
val modify_number : (int option -> int option) -> name -> name

type module_id = int

(** A constant identifier for types *)
type cid_typ = module_id * int

(** A constant identifier for terms *)
type cid_term = module_id * int

(** A constant identifier for schemas *)
type cid_schema = module_id * int


(** A constant identifier for coercions *)
type cid_coercion = module_id * int

(** A constant identifier for computation-level data-types *)
type cid_comp_typ = module_id * int

(** A constant identifier for computation-level codata-types *)
type cid_comp_cotyp = module_id * int

(** A constant identifier for computation-level constructors *)
type cid_comp_const = module_id * int

(** A constant identifier for computation-level destructors *)
type cid_comp_dest = module_id * int

(** A constant identifier for type synonyms. *)
type cid_comp_typdef = module_id * int

(** A constant identifier for recursive computations/programs *)
type cid_prog = module_id * int

(** A constant identifier for a group of mutually proven theorems. *)
type cid_mutual_group = int

(** An offset to be used during shifting for a DeBruijn variable
    representation *)
type offset = int

(** The DeBruijn representation of a variable *)
type var = int


type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | SVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of name
  | SomeString of string

(** Smart constructor for `name'.
    `mk_name' generates a `name' with a guaranteed unique `string'. *)
val mk_name : ?loc:Location.t -> ?modules:string list ->
              name_guide -> name

val string_of_name : name -> string
val render_name : name -> string
val print : Format.formatter -> name -> unit

(** Prints a list of space-separated names.
    This printer does not open a box!
 *)
val print_list : Format.formatter -> name list -> unit

(** Decide whether two names represent the same thing.
    This simply compares the string representations of the names. This
    corresponds with a user's intuition about when names are equal,
    and ignores all name generation hinting built in to the `name`
    type.
 *)
val equals : name -> name -> bool

(** Decides equality of two cids, of any kind. *)
val cid_equals : module_id * int -> module_id * int -> bool
