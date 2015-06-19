(** A `name' represents the original named representation of a
    variable.  These are primarily used in parsing and pretty-
    printing.  Names should never be constructed directly.
    See `mk_name'. *)
type name     = private {
  modules : string list;
  string_of_name : string ;
  was_generated : bool;
  counter : int;
}

val inc : name -> name
val gen_fresh_name : name list -> name -> name

type module_id = int

(** A constant identifier for types *)
type cid_typ  = module_id * int

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

(** A constant identifier for recursive computations/programs *)
type cid_prog = module_id * int


(** An offset to be used during shifting for a DeBruijn variable
    representation *)
type offset   = int

(** The DeBruijn representation of a variable *)
type var      = int


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
val mk_name : ?modules:string list -> name_guide -> name
