This document outlines Beluga's proof-search engine. The code can be found in ``src/core/logic.ml``.

There are 2 parts to proof search for Beluga's logic: an outer search loop that performs proof search over the computation types, and an inner loop, that performs LF proof search. In ``src/core/logic.ml``, there are respectively 2 functions that perform these searches. ``cgSolve`` (outer) and ``gSolve`` (inner).

``cgSolve``
-------
Performs a bounded-depth-first focused search over atomic (box and inductive/stratified), arrow, and universal computation types. This loop iterates through a deterministic phase (uniform left and right) and several non-deterministic phases (lemma application/blurring, focusing, splitting/induction). The loop will end when all branches of the tree have been exhausted or a proof is found. A depth bound is given to the loop, and depth is incremented when we switch to solving the precondition(s) of a goal.

  Limitations:
    - incomplete support for parameter and substitution variables

  Issues:
    - incorrect I.H. generation
      - on occassion, one or more incorrect I.H. are generated
      - will cause issues during induction hypothesis application
      - found to be an issue when the inductive argument is nested in the theorem (i.e. not the leftmost univerally quantified arg or leftmost argument in an implication)

    - there are two lists that keep track of the (meta-)variables that have been, or have yet to be split on (``cG_a`` and ``cD_a``). These lists get updated after a split has been made. Currently, the ``cD_a`` does not get updated correctly, as there is no way (that I have found) to know which meta-variables are explicit in the new generated ``cD``. Adding all new meta-variables will cause type check errors in the final program, if an implict meta-variable get split on. To prevent this, it is currently taking an incomplete list of the new explicit variables that get introduced during a split. This causes some proofs to fail automatically (ex. ``t/harpoon/nats_and_bools_auto_invert.input``)

    - when a split on a box type is made, the case pattern uses as its LF context the ``dctx_hat`` (instead of ``dctx``). As an example, if the ``dctx`` is ``(g, x : term)`` then the ``dctx_hat`` becomes something like ``(g, x1)`` and when type reconstruction happens, it thinks ``x1`` is the ``dctx`` and because ``(x1: _)`` is more general than ``(x: term)`` it causes an error. This must be fixed when we print the proof term to the file. We must take the ``dctx`` instead of the ``dctx_hat``. I believe the issue has been previously recorded here: https://github.com/Beluga-lang/Beluga/issues/231

  Future Work:
    - add a blurring/lemma application phase over theorems

``gSolve``
------
Performs a bounded depth-first focused search over LF types. Similarly as above, this loop iterates through a deterministic and non-deterministic phase (focusing). The loop will end when all branches of the tree have been exhausted or a proof is found. A depth bound is given to the loop, and depth is incremented when we switch to solving the precondition(s) of a goal. When called from the outer loop ``cgSolve``, the bound is defaulted to ``3``, which is quite high but allows for *most* proofs to be found. 

  Limitations:
    - Incomplete solving of substitutions
        - currently, we only look for substitutions in the meta-context
