.. _prover-structure:

Prover Structure
================

TODO describe structure of Harpoon interactive: session, theorem, subgoal.

Session
-------

.. _changing sessions:

Changing sessions
^^^^^^^^^^^^^^^^^

One can switch between subgoals, theorems, and sessions mainly by using the
:ref:`select <cmd-select>` command, but changing sessions is a somewhat delicate
process.  All theorems belonging to sessions other than the active session are
*hidden*.
This prevents a theorem in one session from referring to an (incomplete) theorem
from another session. Crucially, this is to prevent undesirable circularities
between theorems.

It is important to be aware of this limitation, as it means that lemmas must be
proven before they can be used.

.. _session configuration wizard:

Session configuration wizard
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Theorem
-------

Subgoal
-------

Show example subgoal prompt. Remark that proof tactics are apply to the current subgoal.
