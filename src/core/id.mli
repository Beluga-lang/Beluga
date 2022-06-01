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

(** Decides equality of two cids, of any kind. *)
val cid_equals : module_id * int -> module_id * int -> bool
