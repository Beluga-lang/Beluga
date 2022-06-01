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

let cid_equals = Pair.equal Int.equal Int.equal
