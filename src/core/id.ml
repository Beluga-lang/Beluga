open Support

type module_id = int

type cid_typ = module_id * int

type cid_term = module_id * int

type cid_schema = module_id * int

type cid_coercion = module_id * int

type cid_comp_typ = module_id * int

type cid_comp_cotyp = module_id * int

type cid_comp_const = module_id * int

type cid_comp_dest = module_id * int

type cid_comp_typdef = module_id * int

type cid_prog = module_id * int

(** Used to identify a group of mutually proven theorems. *)
type cid_mutual_group = int

type offset = int

type var = int

let cid_equal = Pair.equal Int.equal Int.equal

let cid_typ_equal = cid_equal

let cid_term_equal = cid_equal

let cid_schema_equal = cid_equal

let cid_coercion_equal = cid_equal

let cid_comp_typ_equal = cid_equal

let cid_comp_cotyp_equal = cid_equal

let cid_comp_const_equal = cid_equal

let cid_comp_dest_equal = cid_equal

let cid_comp_typdef_equal = cid_equal

let cid_prog_equal = cid_equal

let cid_mutual_group_equal = Int.(=)
