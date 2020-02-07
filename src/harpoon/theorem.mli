open Beluga
open Syntax.Int.Comp

module CompS = Store.Cid.Comp

module Conf : sig
  type t
  val make : Id.name -> order total_dec_kind -> typ -> int -> t
end

type t
type theorem = t

type 'a subgoal_hook = proof_state -> 'a

(**
   TODO
   hide this from outside of this module
 *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

val get_name : t -> Id.name
val has_name_of : t -> Id.name -> bool
val has_cid_of : t -> Id.cid_prog -> bool
val theorem_statement : t -> typ

val serialize : Format.formatter -> t -> unit

val next_subgoal : t -> proof_state option
val select_subgoal_satisfying : t -> (proof_state -> bool) -> proof_state option
val dump_proof : Format.formatter -> t -> unit
val show_proof : t -> unit
val show_subgoals : t -> unit

val add_subgoal : t -> proof_state -> unit
val remove_subgoal : t -> proof_state -> unit
val defer_subgoal : t -> unit

val solve : proof_state -> proof -> unit
val solve_by_replacing_subgoal : t -> proof_state -> (proof -> proof) -> proof_state -> unit
val rename_variable : Id.name -> Id.name -> [ `comp | `meta ] -> t -> proof_state -> unit

val configure : Id.cid_comp_const -> Format.formatter -> (t -> unit subgoal_hook) list ->
                proof_state -> proof_state list -> t
val configure_set : Format.formatter -> (t -> unit subgoal_hook) list -> Conf.t list ->
                    CompS.mutual_group_id * t list
val set_hidden : t -> bool -> unit

val translate : t -> exp_chk
