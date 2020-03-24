.. _undo:

Undo
=====

Harpoon includes an ``undo`` command to revert previous actions. Undo history is
stored on a per-theorem basis, so ensure that the correct theorem is selected
when executing ``undo``.
Only commands that effect a change to the subgoal list can be
undone. Concretely, this means that :ref:`administrative commands` cannot be
undone, since they do not introduce nor eliminate subgoals.

Harpoon also includes a command ``redo`` that will undo the effect of the last undo
command. If a change to the subgoal list is effected, the redo history is
purged. In other words, the history is stored linearly and no "undo tree"
is available.

To see the state of the history, use the ``history`` command. This will show the
history of commands that can be undone as well as whether any commands that can
be redone.

Limitations
-----------

Undo cannot undo things such as creating new sessions. It also cannot undo the
command that completes a proof, as beyond that point there is no more
subgoal prompt through which the user could type ``undo``.

Serializing the current Harpoon state will also cause the undo history to be
lost. This is because serialization will cause Harpoon to reload all state from
the signature. From Harpoon's point of view, the list of subgoals it then has
comes simply from the signature, not from a history of tactics.

To work around these limitations, we currently suggest manually undoing the
offending actions by editing the :ref:`proof script <structured proof language>`.
