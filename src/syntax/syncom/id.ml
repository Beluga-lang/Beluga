open Support

module type ID = sig
  type t

  val of_int : int -> t

  val to_int : t -> int

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t

  module Hashtbl : Hashtbl.S with type key = t

  include Eq.EQ with type t := t

  include Ord.ORD with type t := t

  include Hash.HASH with type t := t

  include Show.SHOW with type t := t
end

module Id_base = struct
  include Int

  let of_int = Fun.id

  let to_int = Fun.id
end

module Module = Id_base
module Typ = Id_base
module Term = Id_base
module Schema = Id_base
module CompTyp = Id_base
module CompCotyp = Id_base
module CompConst = Id_base
module CompDest = Id_base
module CompTypdef = Id_base
module Prog = Id_base
module MutualGroup = Id_base

type module_id = Module.t

type cid_typ = Typ.t

type cid_term = Term.t

type cid_schema = Schema.t

type cid_comp_typ = CompTyp.t

type cid_comp_cotyp = CompCotyp.t

type cid_comp_const = CompConst.t

type cid_comp_dest = CompDest.t

type cid_comp_typdef = CompTypdef.t

type cid_prog = Prog.t

(** Used to identify a group of mutually proven theorems. *)
type cid_mutual_group = MutualGroup.t

type offset = int

type var = int

let cid_equal = Int.equal

let cid_typ_equal = cid_equal

let cid_term_equal = cid_equal

let cid_schema_equal = cid_equal

let cid_comp_typ_equal = cid_equal

let cid_comp_cotyp_equal = cid_equal

let cid_comp_const_equal = cid_equal

let cid_comp_dest_equal = cid_equal

let cid_comp_typdef_equal = cid_equal

let cid_prog_equal = cid_equal

let cid_mutual_group_equal = Int.( = )
