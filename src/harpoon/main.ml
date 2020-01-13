(** Harpoon

@author Jacob Thomas Errington
@author Clare Jang
@author Marcel Goh

Harpoon is an interactive mode for Beluga that uses a small set of
tactics for elaborating proofs.
The syntax of Harpoon proofs is defined in Syntax.Ext.Comp; it is a
part of the computation language.

A Harpoon sessions is a sequence of statements, of which there are two kinds:
1. Commands: these generally manipulate the context in some way,
   e.g. by invoking an IH or a lemma, unboxing an expression to a
   metavariable, etc.
2. Directives: these are proof tactics, which allow for more
   complex formulas to be proven by breaking them apart.
   e.g. intros & split

Harpoon proofs end in two ways:
1. With QED, when the goal has been established.
2. With Incomplete, when the proof still needs work. Incomplete proofs
   are called _subgoals_, since they are typically introduced by using
   tactics.

Tactics (may) solve the current goal at the expense of introducing one
or more subgoals that need to be solved. For example, when focusing on
a subgoal of function type, the `intros` tactic will solve it by
introducing an Incomplete hypothetical derivation that will need to be
solved.

Here is an example (partial) proof.

```
proof modus_ponens : {A : [ |- tp]} {B : [ |- tp]}
                     [ |- nd A ] -> [ |- nd (imp A B) ] -> [ |- nd B ] =
  intros
  { A : [ |- tp ], B : [ |- tp ]
  | a : [ |- nd A], ab : [ |- nd (imp A B) ];
    ?
  };
```
 *)

module B = Beluga

let realMain () =
  B.Debug.init (Some "debug.out");
  let (arg0 :: args) = Array.to_list Sys.argv in
  let options = Options.parse_arguments args |> Options.validate |> Options.elaborate in
  let open Options in
  Prover.start_toplevel
    options.test_stop
    (InputPrompt.create options.test_file options.test_start)
    Format.std_formatter

let main () =
  try
    realMain ()
  with
  | e -> print_string (Printexc.to_string e)

let _ =
  main ()
