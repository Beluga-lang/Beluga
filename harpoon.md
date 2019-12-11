Harpoon
-------

Harpoon is an interactive proof assistant for Beluga. It aims to make proving in
Beluga simpler by streamlining proofs into a small set of tactics. Instead of
fretting over the syntax of Beluga terms, the programmer can instead focus on
the formulas being manipulated.

### Usage

#### Starting Harpoon

Start the Harpoon interactive mode by using `bin/harpoon --implicit --sig SIG` where `SIG`
is the name of the signature file you will use as a context of your theorem.

* You will be prompted for some details of the theorems to prove.
  * You will be prompted for the name of theorem to prove.
    When you have no more theorem to prove, put just enter key in.
  * You will be prompted for the statement of the theorem to prove: this is a
    Beluga type, e.g. `[|- oft M A] -> [|- eval M M'] -> [|- oft M' A]`.
    Note that free variables will automatically be pibox-quantified at the front.
  * You will be promped for the induction order, i.e. which argument you are doing
    induction on. This is an optional number, starting at `1`.
    In the case of the above example `tps`, you should enter `2`, since the
    theorem is proven by induction on the evaluation judgment `[|- eval M M']`.
    If you do not want any induction, put just enter key in.

You should then arrive at the Harpoon prompt, which is a lambda.

#### Harpoon Commands

Harpoon operates internally on a list of open subgoals.
The lambda prompt is presented in the context of a current subgoal:
all computational and metavariables will be listed along with their types.
Initially, the only subgoal is the whole theorem, with all the assumptions
introduced. (See the section _Automatic Tactics_ for why.)

The following are the commands in Harpoon.

Administrative commands:
* `show-proof`: dumps the entire proof as text.
* `rename`: rename a variable
* `defer`: go to the next subgoal
* `show-ihs`: dumps the currently available induction hypotheses.
* `show-subgoals`: lists all open subgoals
* `toggle-automation KIND`: enables/disables the automatic tactic `KIND`.
  Supported values of `KIND` are: `auto-intros`, `auto-solve-trivial`.
  These are described in the section _Automatic Tactics_

The following are the proof tactics. In these commands, `E` denotes a
computational expression.

* `intros [NAMES...]`: introduces the assumptions of the current subgoal.
  Explicit names can be optionally given to the assumptions. If no names are
  specified, then names are generated automatically.
* `split E`: perform case analysis on the expression `E`.
  (Technically, `E` must be a _synthesizable_ expression.)
* `invert E`: identical to `split`, but it is checked that there is exactly one
  split.
* `by C (E) as x`: invoke the expression `E` and bind the result as the
  computational variable `x`.
  Supported values of `C` are: `ih` and `lemma`.
  e.g. if we are proving `tps`, then we may want to invoke the induction
  hypothesis as `by ih (tps [|- D] [|- E]) as r`
* `unbox (E) as X`: assuming `E` is of box-type, defines a metavariable `X` with
  the same type.
  (`E` must be a synthesizable expression.)
* `solve E`: solve the current subgoal with the expression `E`.

### Automatic Tactics

Some tactics in Harpoon can be performed eagerly without affecting the
provability of the goal. Whenever a new subgoal is created, Harpoon will
automatically apply these tactics, subject to whether they are enabled.
(See the section _Harpoon Commands_ for the description of the
`toggle-automation` command.)

The following are the available automatic tactics.
* `auto-intros`: subgoals will automatically have all assumptions introduced
  with automatically generated names.
* `auto-solve-trivial`: trivial subgoals will be solved automatically.
  A subgoal is _trivial_ if the goal is present as an assumption.

### Example

* Start the Harpoon interactive mode with the simply-typed lambda calculus:
  `bin/harpoon --implicit --sig examples/stlc.bel`
* Input some detail of the theorem starting from its name: `tps`
* Input the statement of the theorem:
  `[ |- oft M A ] -> [ |- eval M M' ] -> [ |- oft M' A ]`
  Free metavariables are permitted in these type signatures, and will
  automatically be abstracted over universally.
* Harpoon should display the current proof state and present you with the right
  angle braket prompt.
  The state should be that all the assumptions of the theorem have been
  introduced.
* Run `show-proof`. You should see that the `--intros` tactic appeared in the
  proof, and that a hypothetical derivation has opened up with all the
  assumptions listed and with a `?` in it.
  This is because of the `auto-intros` automatic tactic having been
  invoked. (See _Automatic Tactics_.)
