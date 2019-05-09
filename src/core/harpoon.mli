(** module Harpoon
 @author Jacob Thomas Errington
 
 This module defines the datatypes for Harpoon syntax and operations
 for transforming it.
 
 A Harpoon script is a sequence of commands, of which there are two kinds:
 1. Statements: these are formulas, each of which must follow from
    preceding formulas.
 2. Directives: these are proof tactics, which allow for more
    complex formulas to be proven than by simply stating them.

 There is a meta syntactic command `?` called a _hole_, which
 represents an open proof obligation.
 Certain commands affect the goal of the proof, typically by involving
 one or more _hypothetical derivations_. These are represented as
 _scopes_, delimited by curly braces { }.

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

 Since the goal of the theo
 *)

module Comp = Syntax.Int.Comp

module Prover : sig
  val start_toplevel : Format.formatter -> string -> Comp.typ -> unit
end
