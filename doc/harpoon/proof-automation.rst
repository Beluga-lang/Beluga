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

--------------------------------------------------------------------------------
The following actions make use of the proof search loop ``cgSolve`` in ``src/core/logic.ml``
Therefore as it's capabilites improve, so should the documentation on these
actions capabilities.

Current limitations:
 - no paramater variables
 - no substitution variables
 - no case splits (>1 case produced)
 - no pair type
 - no splitting on contexts

.. _auto invert solve:

``auto-invert-solve``
----------------------

This automation attempts to solve the subgoal if no variable splitting (other than inversions) is required to solve
the goal. It performs 2 iterations of depth-first proof-search, once on the computation level, and
once again on the LF level. Use ``auto-invert-solve INT`` to specify the maximum depth
you want your search tree to reach. Depth is incremented when we attempt to
solve a subgoal.

For example, if we want to solve ``Ev [|- S (S (S (S z)))]`` this would require
a depth bound of at least 2:::

   inductive Ev : [⊢ nat] → ctype =
   | ZEv : Ev [⊢ z]
   | SEv : Ev [⊢ N] → Ev [⊢ S (S N)]

   depth = 0
   solve for Ev [|- S (S (S (S z)))] -> focus on SEv --->

   depth = 1
   solve for Ev [|- S (S z)] -> focus on SEv --->

   depth = 2
   solve for Ev [|- z] -> focus on zEv

   Note: If a goal has more than one subgoal, depth only increments by 1.

   For example, if we want to solve ``Less_Than [|- S z] [|- S (S (S z))]`` this
   would require depth bound of 3:

   inductive Less_Than : [⊢ nat] → [⊢ nat] → ctype =
   | ZLT : Less_Than [⊢ z] [⊢ S N]
   | LT : Less_Than [⊢ N] [⊢ M] → Less_Than [⊢ S N] [⊢ S M]
   | Trans_LT : Less_Than [⊢ N] [⊢ M]
                  → Less_Than [⊢ M] [⊢ K] → Less_Than [⊢ N] [⊢ K]

   depth = 0
   solve for Less_Than [|- S z] [|- S (S (S z))] -> focus on Trans_LT --->

      depth = 1
      solve for Less_Than [|- M] [|- S (S (S z))] -> focus on LT --->

         depth = 2
         solve for Less_Than [|- M'] [|- S (S z)] -> focus on LT --->
   
            depth = 3
            solve for Less_Than [|- M''] [|- S z] -> focus on ZLT

      ---> found LT LT ZLT : Less_Than [|- S (S z)] [|- S (S (S z))]

      depth = 1
      solve for Less_Than [|- S z] [|- S (S z)] -> focus on LT --->

         depth = 2
         solve for Less_Than [|- z] [|- S z] -> focus on ZLT

      ---> found LT ZLT : Less_Than [|- S z] [|- S (S z)]

   -> found Trans_LT (LT ZLT) (LT LT ZLT) : Less_Than [|- S z] [|- S (S (S z))]

.. _inductive auto solve:

``inductive-auto-solve``
------------------------

This automation will perform a case split on the user-specified variable then call auto-invert-solve on each sub case.  Use ``inductive-auto-solve INT`` to specify the maximum depth you want your search tree to reach. Depth is incremented as above.
