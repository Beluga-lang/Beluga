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

(** Tactics operate on an incomplete proof in a tactic context.
    They may choose to solve the goal by removing it or add new subgoals, or both.
 *)
type t = Theorem.t -> Comp.proof_state -> unit

(** Solves the subgoal with the given proof. *)
val solve : Comp.proof -> t

(** Introduces the arguments to a function type, with the given names, if any. *)
val intros : string list option -> t

type intros'_failure =
  | DuplicatedNames
  | NothingToIntro

(** Introduces the arguments to a function type, with the given names, if any. *)
val intros' : Theorem.t ->
              string list option -> Beluga.Syntax.Int.LF.mctx -> Comp.gctx -> Comp.typ ->
              (intros'_failure, Beluga.Syntax.Int.LF.mctx * Comp.gctx * Comp.typ) Support.Either.t

(** Performs a case analysis on the given synthesizable expression of
    the given type.
    The split_kind is used to perform an additional check on the
    split, regarding the number of branches.
    In particular, this is used to implement variants of splitting,
    e.g. inversion and impossible.
 *)
val split : Command.split_kind -> Comp.exp_syn -> Comp.typ -> Comp.total_dec list -> t

(** Performs unboxing of the given synthesizable expression of the given type.
    The tactic will itself verify that the type is a box-type.
 *)
val unbox : Comp.exp_syn -> Comp.typ -> Id.name -> t

(** It is verified that the given expression is an application.
    The result of the invocation is assigned to the variable of the
    given name, in cG, in case the given boxity is (the default)
    `boxed.
    Otherwise, with `unboxed, the name is a new variable declaration
    in cD.
 *)
val invoke : Comp.boxity -> Comp.exp_syn -> Comp.typ -> Id.name -> t

(** Solves the current goal with an implication whose conclusion is
   compatible with the goal type. Subgoals are generated for each
   premise of the implication.

    The user needs to decide upfront what the types of all the
   premises are, and these given types must unify with the
   corresponding premise types. Furthermore, this unification must pin
   down all universally quantified variables, as there is no way to
   construct them using Harpoon. (Harpoon can only construct
   computational objects, not LF objects.)

    Another restriction is that *all* universally quantified variables
   must appear at the beginning. That is, the type `tau` must be of
   the form

    tau = Pi X_1:U_1. ... Pi X_n:U_n. tau_1 -> ... -> tau_k -> tau'

    (This is most common form of type for a Beluga function.)

    Subject to the following requirements:
    - cD; cG |- i ==> tau
    - tau' unifies with the current goal type.
    - each tau_i unifies with the corresponding type in the args list.

    After all these unifications, there must be no remaining
    universally quantified variables. (Such a type would be very
    strange, so this requirement is quite weak.)

    The concrete syntax of this command piggybacks off the syntax of
    `by` is

    by <lemma/ih> i suffices tau_1, ..., tau_k
 *)
val suffices : Comp.exp_syn -> Comp.typ list -> Comp.typ -> t
