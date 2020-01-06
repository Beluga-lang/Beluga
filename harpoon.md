Harpoon
-------

Harpoon is an interactive proof assistant for Beluga. It aims to make proving in
Beluga simpler by streamlining proofs into a small set of tactics. Instead of
fretting over the syntax of Beluga terms, the programmer can instead focus on
the formulas being manipulated.

## Usage

### Starting Harpoon

Start the Harpoon interactive mode by using `bin/harpoon --implicit --sig SIG` where `SIG`
is the name of the signature file you will use as a context of your theorem.

A Harpoon instance is broken up into a hierarchical structure:
* A _session_ consists of multiple theorems being proven mutually.
* A _theorem_ consists of multiple open subgoals that must be solved.
* A _subgoal_ is the basic unit of work in Harpoon, and all proper tactics
  affect the currently active subgoal.

When Harpoon starts, it runs the _session configuration wizard_, with which you
interactively configure the theorems to prove in the default session.
For each theorem, you must provide:
* The name of the theorem. To finish configuration, leave an empty name and
  press the return key.
* The statement of the theorem. This is a Beluga type, subject to automatic
  abstraction for implicit parameters,
  e.g. `[|- oft M A] -> [|- eval M M'] -> [|- oft M' A]` will have the free
  (meta)variables `M`, `A`, and `M'` universally quantified.
* The termination measure for the theorem. Currently, Beluga only supports
  structural recursion on a single argument. This argument is specified by
  number in this prompt. For type preservation, we proceed by induction on the
  evaluation judgment, which is the second argument to the theorem, so you would
  write `2` for the termination measure.
  In other words, the 1-indexed argument number is given without counting
  implicit arguments.

With session configuration finished, the main Harpoon prompt appears.

### Harpoon Commands

Harpoon operates internally on a list of open subgoals.
The Harpoon prompt is presented in the context of a current subgoal, theorem,
and session:
all computational and metavariables will be listed along with their types.
Initially, the only subgoal is the whole theorem, with all the assumptions
introduced. (See the section _Automatic Tactics_ for why.)

#### Administrative commands

These are commands that do not advance the proof, but instead serve to manage
the current proof and the proof assistant.

* `rename`: rename a variable.
* `toggle-automation KIND`: enables/disables the automatic tactic `KIND`.
  Supported values of `KIND` are: `auto-intros`, `auto-solve-trivial`.
  These are described in the section _Automatic Tactics_
* `type E`: show the type of the (synthesizable) expression `E`.

All remaining administrative commands are broken up according to whether they
affect the active session, theorem, or subgoal.

* `session COMMAND` affects the current session.
  The following options are possible for `COMMAND`:
  - `defer`: switch to the next session.
  - `list`: list all sessions.
  - `select NAME`: select a session by name.
  - `create NAME`: create a new session with the given name.
* `theorem COMMAND` affects the current theorem.
  The following options are possible for `COMMAND`:
  - `defer`, `list`, `select NAME`: behave as for `session`.
  - `show-ihs`: list available induction hypotheses.
  - `show-proof`: display theorem's (partial) proof script.
* `subgoal COMMAND`: affects the current subgoal.
  The following options are possible for `COMMAND`:
  - `defer`, `list`: same as for `theorem` and `session`.

Since deferring the current subgoal is the most common type of defer, the
toplevel command `defer` is a shortcut for `subgoal defer`.

#### Tactic commands

The following are the proof tactics. In these commands, `E` denotes a
computational expression.

* `intros [NAMES...]`: introduces the assumptions of the current subgoal.
  Explicit names can be optionally given to the assumptions. If no names are
  specified, then names are generated automatically.
* `split E`: perform case analysis on the expression `E`.
  The current subgoal is eliminated and one new subgoal is generated for every
  case.
* `invert E`: identical to `split`, but it is checked that there is exactly one
  case.
* `impossible E`: identical to `split`, but it is checked that there are exactly
  zero cases.
* `unbox E as X`: assuming `E` is of box-type, defines a metavariable `X` with
  the same type.
* `by C E as x [unboxed]`: invoke the expression `E` and bind the result
  as the variable `x`.
  If the `unboxed` keyword is given, then the variable `x` is a new metavariable
  (in the meta-context); else, `x` is a new computational variable.
  Choices for `C` are: `ih` and `lemma`.
  e.g. if we are proving `tps`, then we may want to invoke the induction
  hypothesis as `by ih tps [|- D] [|- E] as r`.
* `suffices by C E toshow T_1, T_2, ..., T_(n-1)`:
  The ordinary `by` command is a forward reasoning tactic, whereas `suffices by`
  is a backward reasoning tactic.
  - Currently, the only supported invocation kind `C` is `lemma`.
  - The expression `E` must synthesize a type of the form:
    `{X_1 : U_1} {X_2 : U_2} ... {X_k : U_k} T_1' -> T_2' -> ... -> T_n'`
  - The given types `T_i` must unify with the corresponding `T_i'`.
  - The current goal type must unify with `T_n'`.
  - The unification must instantiate all universally quantified variables `X_j`.
  The current subgoal is removed, and one subgoal is added for each of the types
  given after `toshow`.
  For example, suppose that the current subgoal is `[|- eq A A]` for
  `A : [|- tp]`; we must prove that that `A` is equal to itself.
  Suppose further that we have the lemma `refl : {X : [|- tp]} [|- eq X X]`. The
  goal can be solved by using `suffices by lemma refl toshow`. `[|- eq X X]`
  will be unified with `[|- eq A A]`, instantiating the (only) universally
  quantified variable `X := A`. There are no subgoals introduced since the lemma
  has no premises.
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
