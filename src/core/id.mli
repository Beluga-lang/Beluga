(** A `name' represents the original named representation of a
    variable.  These are primarily used in parsing and pretty-
    printing.  Names should never be constructed directly.
    See `mk_name'. *)
type name     = private {
  modules : string list;
  string_of_name : string ;
  was_generated : bool
}

(** cid_ now includes a first string list for the module begin referenced by this call
    (i.e. [Nats] if orignal was Nats.z) and 2nd list referring to original decleration
    (which would be [Nats] if it was defined in a module Nats.

    cids will be considered equal if the 2nd string list and the int are equal *)


(** A constant identifier for types *)
type cid_typ  = string list * string list * int

(** A constant identifier for terms *)
type cid_term = string list * string list * int

(** A constant identifier for schemas *)
type cid_schema = string list * string list * int


(** A constant identifier for coercions *)
type cid_coercion = string list * string list * int

(** A constant identifier for computation-level data-types *)
type cid_comp_typ = string list * string list * int

(** A constant identifier for computation-level codata-types *)
type cid_comp_cotyp = string list * string list * int

(** A constant identifier for computation-level constructors *)
type cid_comp_const = string list * string list * int

(** A constant identifier for computation-level destructors *)
type cid_comp_dest = string list * string list * int

(** A constant identifier for recursive computations/programs *)
type cid_prog = string list * string list * int


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
