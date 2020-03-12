.. _proof automation:

Proof automation
================

Harpoon provides rudimentary automation for basic tasks during proofs.
Each automation type can be controlled via the ``toggle-automation``
:ref:`tactic <cmd-toggle-automation>`.

Automations run at the moment that a new subgoal is created.

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
