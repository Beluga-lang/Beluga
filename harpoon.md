Harpoon
-------

Harpoon is an interactive proof assistant for Beluga. It aims to make proving in
Beluga simpler by streamlining proofs into a small set of tactics. Instead of
fretting over the syntax of Beluga terms, the programmer can instead focus on
the formulas being manipulated.

### Usage

First, start Beluga in interactive mode and with implicit argument printing
enabled by running `bin/beluga +implicit -I`.
The Harpoon interactive mode is started from the basic interactive
mode by using the `%:prove` command and entering the statement of a
theorem to prove. The Harpoon interactive mode's prompt is a lambda.

Currently, only the `intros` tactic is implemented, and will introduce
all the assumptions into the context.
The `show-proof` command will display the current proof script.

### Example

* Start the Beluga interactive mode: `bin/beluga +implicit -I`
* Load the simply-typed lambda calculus: `%:load examples/stlc.bel`
  You should see a message confirming the loading, and Beluga should print out
  the internal representation of the file.
* Begin the Harpoon interactive mode, by giving a name to the theorem:
  `%:prove tps`
* Input the statement of the theorem:
  `[ |- oft M A ] -> [ |- eval M M' ] -> [ |- oft M' A ]`
  Free metavariables are permitted in these type signatures, and will
  automatically be abstracted over universally.
* Harpoon should display the current proof state and present you with the lambda
  prompt.
* If you run `show-proof` right now, you should just see a question mark,
  indicating that the current proof is empty.
* Run `intros`. All the assumptions should be introduced.
  This includes metavariables and computation variables.
* Run `show-proof`. You should see that the `--intros` tactic appeared in the
  proof, and that a hypothetical derivation has opened up with all the
  assumptions listed and with a `?` in it.

