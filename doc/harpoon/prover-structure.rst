.. _prover-structure:

Prover Structure
================

Harpoon is structured in a hierarchical fashion: the prover
maintains a number of *sessions*, each contains a number of
*theorems*, each of which contains a number of *subgoals*.
A theorem with no subgoals remaining is *complete*, and
similarly, a session with no theorems remaining is *complete*.

.. _session:

Session
-------

Harpoon organizes a set of mutually inductive theorems into a *session*. Often,
there is only one session at a time in Harpoon, but more than one simultaneous
session is possible. For example, you might want to start a second session if
you decide to prove a lemma while in the middle of another proof.

.. _changing sessions:

Changing sessions
^^^^^^^^^^^^^^^^^

One can switch between theorems by using the :ref:`select <cmd-select>`
command. Selecting a theorem belonging to another session will cause a *session
switch*, which is a somewhat delicate process.

In order to prevent incomplete theorems in different sessions from referring to
each other, all theorems belonging to other sessions are not in scope. When
switching sessions, the theorems in the active session are moved out of scope,
and the theorems in the destination session are brought into scope.
Crucially, this is to prevent undesirable circularities between theorems.

It is important to be aware of this limitation, as it means that lemmas must be
proven before they can be used.

.. _session configuration wizard:

Session configuration wizard
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The series of interactive prompts that appear when Harpoon is started is called
the *session configuration wizard*. This wizard appears when there are no
sessions in the prover, and unless there were incomplete proofs in the loaded
signature, there will be no sessions when Harpoon starts.

The wizard prompts for three things about each theorem:

1. The name of the theorem. This is how the theorem is referred to for induction
   hypotheses, and how other theorems can refer to this theorem.
2. The statement of the theorem. This is a Beluga computational type.
   (See :ref:`Contextual LF`.)
3. The induction order of the theorem. Non-inductive theorems can simply leave
   this blank. Inductive theorems specify the order numerically, by giving the
   position of the parameter to induct on. Only explicit parameters are counted,
   and counting proceeds from left to right.

.. note::

    Implicit context quantifiers are not counted for the
    numeric induction order. That is, in

    .. code-block:: Beluga

      (g : ctx) [g |- oft M A] -> [g |- step M M'] -> [g |- oft M' A]

    the position of the parameter of type ``[g |- step M M']`` is still ``2``.

For example, here is how one might configure a type preservation proof for the
simply-typed lambda calculus.

.. code-block:: text

    Name of theorem: tps
    Statement of theorem: [|- oft M A] -> [|- step M M'] -> [|- oft M' A]
    Induction order: 2

Once a theorem is configured, the wizard will repeat so you can configure
additional theorems to be proven mutually. To end the wizard, use an empty
theorem name or the special name ``:quit``. Ending the wizard without
configuring any theorems will abort the creation of the new session. If there
are no other sessions in Harpoon, then Harpoon will exit.

.. _subgoal:

Subgoal
-------

Proofs are developed by applying a tactic to a subgoal. If the tactic is
successful, the subgoal it is applied to is *solved* and removed from its
theorem. New subgoals may be introduced by the tactic. These subgoals are
understood as children of the subgoal that was eliminated.

Subgoal prompt
^^^^^^^^^^^^^^

To apply a tactic, one types the corresponding command into the *subgoal
prompt*. This prompt is the main point of interaction with Harpoon. Consider
this example subgoal prompt from the beginning of a type preservation proof for
the simply-typed lambda calculus.

.. code-block:: text

    intros
    Meta-context:
      M : ( |- tm) (not in scope)
      A : ( |- tp) (not in scope)
      M' : ( |- tm) (not in scope)
    Computational context:
      x : [ |- oft M A]
      x1 : [ |- step M M']

    -------------------------------
    [ |- oft M' A]

    >

The subgoal prompt shows the prover state at the subgoal. This state contains
three key pieces of information.

1. The subgoal label. Every subgoal in Harpoon is identified by a *subgoal
   label*. This label indicates where in the proof this subgoal is located. In
   the example, the label is ``intros`` at the very top,
   and demonstrates that this subgoal is right after having introduced the
   assumptions of the theorem.
2. The contexts. Harpoon uses Beluga's
   :ref:`indexed type system <Contextual LF>` in which one
   distinguishes between metavariables and computational
   variables. Metavariables belong to the meta-context and computational
   variables belong to the computational context. Notice that the metavariables
   in the example are all marked ``(not in scope)``. This
   annotation is presented for implicit parameters: recall that in the statement
   of the theorem, the parameters ``M``, ``A`` and ``M'`` appeared free.
3. The goal. Below the line, the type of the subgoal appears. As tactics are
   applied and new subgoals are introduced, one can expect the goal type to
   change. Broadly speaking, one's objective is to construct a term of this
   type.

Administrative tactics
^^^^^^^^^^^^^^^^^^^^^^

There are a number of tactics in Harpoon that do not contribute directly to the
development of the proof, but are used to manipulate the state of the
prover. To distinguish these from the *proof tactics*, we call these
*administrative tactics*. Despite not contributing to the development of the
proof, administrative tactics are nonetheless entered into the subgoal prompt.

See :ref:`here <administrative commands>` for the complete list of
administrative tactics.
