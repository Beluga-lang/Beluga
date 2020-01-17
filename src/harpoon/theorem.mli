open Beluga
open Syntax.Int.Comp

module Conf : sig
  type t
  val make : Id.name -> order option -> typ -> t
end

type t
type theorem = t

(**
   TODO
   hide this from outside of this module
 *)
val printf : t -> ('a, Format.formatter, unit) format -> 'a

val get_name : t -> Id.name
val has_name_of : t -> Id.name -> bool
val has_cid_of : t -> Id.cid_prog -> bool
val theorem_statement : t -> typ

val next_subgoal : t -> proof_state option
val show_proof : t -> unit
val show_subgoals : t -> unit

val add_subgoal : t -> proof_state -> unit
val remove_subgoal : t -> proof_state -> unit
val defer_subgoal : t -> unit

val solve : proof_state -> proof -> unit
val solve_by_replacing_subgoal : t -> proof_state -> (proof -> proof) -> proof_state -> unit
val rename_variable : Id.name -> Id.name -> [ `comp | `meta ] -> t -> proof_state -> unit

val configure_set : Format.formatter -> (t -> proof_state -> unit) list -> Conf.t list -> t list
val total_dec : t -> Total.dec
val set_hidden : t -> bool -> unit
