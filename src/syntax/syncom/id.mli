(** Constant IDs for referring to constants in the global mutable store.

    These are essentially primary keys in a relational database. *)

(** Definition of IDs as an abstract integer.

    This prevents mixing up the various ID types. *)
module type ID = sig
  type t

  val of_int : int -> t

  val to_int : t -> int
end

module Module : ID

module Typ : ID

module Term : ID

module Schema : ID

module CompTyp : ID

module CompCotyp : ID

module CompConst : ID

module CompDest : ID

module CompTypdef : ID

module Prog : ID

module MutualGroup : ID

type module_id = Module.t

(** A constant identifier for types *)
type cid_typ = Typ.t

(** A constant identifier for terms *)
type cid_term = Term.t

(** A constant identifier for schemas *)
type cid_schema = Schema.t

(** A constant identifier for computation-level data-types *)
type cid_comp_typ = CompTyp.t

(** A constant identifier for computation-level codata-types *)
type cid_comp_cotyp = CompCotyp.t

(** A constant identifier for computation-level constructors *)
type cid_comp_const = CompConst.t

(** A constant identifier for computation-level destructors *)
type cid_comp_dest = CompDest.t

(** A constant identifier for type synonyms. *)
type cid_comp_typdef = CompTypdef.t

(** A constant identifier for recursive computations/programs *)
type cid_prog = Prog.t

(** A constant identifier for a group of mutually proven theorems. *)
type cid_mutual_group = MutualGroup.t

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
