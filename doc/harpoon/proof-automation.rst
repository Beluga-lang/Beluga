.. _proof automation:

Proof automation
================

Harpoon provides rudimentary automation for basic tasks during proofs.
Each automation type can be controlled via the ``toggle-automation``
:ref:`tactic <cmd-toggle-automation>`.

Automations run at the moment that a new subgoal is created.

Actions performed by automatic tactics can be :ref:`undone <undo>`.

.. _auto intros:

``auto-intros``
---------------

This automation introduces assumptions into the context whenever the subgoal has
a function type.

.. _auto solve trivial:

``auto-solve-trivial``
----------------------

This automation solves subgoals in which the context contains an assumption
whose type is convertible with goal type.

It will never solve the last remaining subgoal in a theorem, as this makes
certain theorems impossible to prove using Harpoon. For example, this is
essential for implementing a function such as ``double : [|- nat] -> [|- nat]``:
``auto-intros`` will bring ``x : [|- nat]`` into the context and
``auto-solve-trivial`` would immediately finish the theorem before the user ever
sees a subgoal prompt.
