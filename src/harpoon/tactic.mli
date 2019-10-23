(** All the high-level proof tactics.
 * In general, a tactic has inputs
 * 1. Some tactic-specific parameters
 * 2. A `proof_state` to act on
 *
 * Tactics are parameterized by a TacticContext that gives them
 * certain capabilities, such as manipulating the subgoal list or
 * showing messages to the user.
 *
 * Tactics are not obligated to solve the current subgoal!
 *)

module Comp = Beluga.Syntax.Int.Comp
module Command = Beluga.Syntax.Ext.Harpoon
module Id = Beluga.Id
module Total = Beluga.Total

(** Capabilities passed to tactics so they can manipulate the
    interpreter state. *)
type tactic_context =
  { add_subgoal : unit Comp.proof_state -> unit
  ; remove_subgoal : unit Comp.proof_state -> unit
  ; remove_current_subgoal : unit -> unit
  ; replace_subgoal : Comp.proof_state -> unit
  ; printf : 'a. ('a, Format.formatter, unit) format -> 'a
  ; defer : unit -> unit
  }

(** Tactics operate on an incomplete proof in a tactic context.
    They may choose to solve the goal by removing it or add new subgoals, or both.
 *)
type t = unit Comp.proof_state -> tactic_context -> unit

(** Solves the subgoal with the given proof. *)
val solve : Comp.incomplete_proof -> t

(** Introduces the arguments to a function type, with the given names, if any. *)
val intros : string list option -> t

(** Performs a case analysis on the given synthesizable expression of
    the given type.
    The split_kind is used to perform an additional check on the
    split, regarding the number of branches.
    In particular, this is used to implement variants of splitting,
    e.g. inversion and impossible.
 *)
val split : Command.split_kind -> Comp.exp_syn -> Comp.typ -> Total.dec list -> t

(** Performs unboxing of the given synthesizable expression of the given type.
    The tactic will itself verify that the type is a box-type.
 *)
val unbox : Comp.exp_syn -> Comp.typ -> Id.name -> t

(** Performs the given invocation, namely of an IH or a lemma,
    according to `invoke_kind`.
    It is verified that the given expression is an application.
    The result of the invocation is assigned to the variable of the
    given name, in cG.
 *)
val invoke : Command.invoke_kind -> Command.boxity -> Comp.exp_syn -> Comp.typ -> Id.name -> t

(** A low-level tactic that replaces the current subgoal with the
    given one, and adds some number of commands to the proof.
    The first proof state is the new one, and the second one is the one to solve.
 *)
val solve_by_replacing_subgoal : Comp.proof_state -> Comp.command list -> t
