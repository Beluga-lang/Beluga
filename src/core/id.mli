(** A `name' represents the original named representation of a
    variable.  These are primarily used in parsing and pretty-
    printing.  Names should never be constructed directly.
    See `mk_name'. *)
type name     = private {
  string_of_name : string ;
  was_generated : bool
}

(** A constant identifier for types *)
type cid_typ  = int

(** A constant identifier for terms *)
type cid_term = int

(** A constant identifier for schemas *)
type cid_schema = int


(** A constant identifier for coercions *)
type cid_coercion = int

(** A constant identifier for computation-level data-types *)
type cid_comp_typ = int

(** A constant identifier for computation-level codata-types *)
type cid_comp_cotyp = int

(** A constant identifier for computation-level constructors *)
type cid_comp_const = int

(** A constant identifier for computation-level destructors *)
type cid_comp_dest = int

(** A constant identifier for recursive computations/programs *)
type cid_prog = int


(** An offset to be used during shifting for a DeBruijn variable
    representation *)
type offset   = int

(** The DeBruijn representation of a variable *)
type var      = int


type name_guide =
  | NoName
  | MVarName of (unit -> string) option
  | PVarName of (unit -> string) option
  | BVarName of (unit -> string) option
  | SomeName of name
  | SomeString of string

(** Smart constructor for `name'.
    `mk_name' generates a `name' with a guaranteed unique `string'. *)
val mk_name : name_guide -> name
