type module_id = int

(** A constant identifier for types *)
type cid_typ = int

(** A constant identifier for terms *)
type cid_term = int

(** A constant identifier for schemas *)
type cid_schema = int

(** A constant identifier for computation-level data-types *)
type cid_comp_typ = int

(** A constant identifier for computation-level codata-types *)
type cid_comp_cotyp = int

(** A constant identifier for computation-level constructors *)
type cid_comp_const = int

(** A constant identifier for computation-level destructors *)
type cid_comp_dest = int

(** A constant identifier for type synonyms. *)
type cid_comp_typdef = int

(** A constant identifier for recursive computations/programs *)
type cid_prog = int

(** A constant identifier for a group of mutually proven theorems. *)
type cid_mutual_group = int

(** An offset to be used during shifting for a DeBruijn variable
    representation *)
type offset = int

(** The DeBruijn representation of a variable *)
type var = int

(** {1 Comparisons} *)

val cid_typ_equal : cid_typ -> cid_typ -> bool

val cid_term_equal : cid_term -> cid_term -> bool

val cid_schema_equal : cid_schema -> cid_schema -> bool

val cid_comp_typ_equal : cid_comp_typ -> cid_comp_typ -> bool

val cid_comp_cotyp_equal : cid_comp_cotyp -> cid_comp_cotyp -> bool

val cid_comp_const_equal : cid_comp_const -> cid_comp_const -> bool

val cid_comp_dest_equal : cid_comp_dest -> cid_comp_dest -> bool

val cid_comp_typdef_equal : cid_comp_typdef -> cid_comp_typdef -> bool

val cid_prog_equal : cid_prog -> cid_prog -> bool

val cid_mutual_group_equal : cid_mutual_group -> cid_mutual_group -> bool
