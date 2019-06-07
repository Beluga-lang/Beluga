(** module Harpoon
@author Jacob Thomas Errington

Harpoon is an interactive mode for Beluga that uses a small set of
tactics for elaborating proofs.
The syntax of Harpoon proofs is defined in Syntax.Ext.Comp; it is a
part of the computation language.
 
This module defines the datatypes for Harpoon syntax and operations
for transforming it.

A Harpoon script is a sequence of statements, of which there are two kinds:
1. Claims: these are formulas, each of which must follow from
   preceding formulas.
   Claims may optionally be named, so that they may be referred to later.
   Claims may optionally be established by giving an explicit term.
2. Directives: these are proof tactics, which allow for more
   complex formulas to be proven than by simply stating them.
   Directives all begin with the `--` marker, e.g. `--intros`,
   `--split`.

Harpoon proofs end in two ways:
1. With QED, when the goal has been established.
2. With Incomplete, when the proof still needs work. Incomplete proofs
   are called _subgoals_, since they are typically introduced by using
   tactics.

Tactics solve the current goal at the expense of introducing one or
more subgoals that need to be solved. For example, when focusing on a
subgoal of function type, the `--intros` tactic will solve it by
introducing an Incomplete hypothetical derivation that will need to be
solved.

Here is an example (partial) proof.

```
proof modus_ponens : {A : [ |- tp]} {B : [ |- tp]}
                     [ |- nd A ] -> [ |- nd (imp A B) ] -> [ |- nd B ] =
begin
  --intros
  { A : [ |- tp ], B : [ |- tp ]
  | a : [ |- nd A], ab : [ |- nd (imp A B) ];
    ?;
    [ |- nd B]
  }
  {A : [ |- tp]} {B : [ |- tp]
  [ |- nd A ] -> [ |- nd (imp A B) ] -> [ |- nd B ]
end;
```
 *)

module Comp = Syntax.Int.Comp

module Prover : sig
  val start_toplevel : Format.formatter -> Id.name -> Comp.tclo -> Comp.order -> unit
end
