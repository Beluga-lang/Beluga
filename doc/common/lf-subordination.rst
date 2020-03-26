.. _lf subordination:

LF Subordination
================

LF declarations in Beluga may or may not refer to earlier declarations.
Therefore, it is possible to ascertain that certain derivations cannot depend on
certain contextual assumptions, and to eliminate these assumptions. As a
concrete example, consider this signature.

.. code-block:: Beluga

    LF unit1 : type =
      | u1 : unit1
    ;

    LF unit2 : type =
      | u2 : unit2
    ;

    schema ctx = block a1 : unit1, a2 : unit2 ;

The schema ``ctx`` consists of blocks (pairs) consisting of a ``unit1`` and a
``unit2``.  Now suppose we have a derivation of type
``g, b : block a1 : unit1, a2 : unit2 |- unit1`` where ``g : ctx``.
This derivation builds a ``unit1``, and by looking at the definition of that
type, we can see that there is no way any ``unit2`` could be involved in the
construction of that derivation.

Strengthening
-------------

Beluga recognizes as legitimate any program that would drop such irrelevant
assumptions: this is called **strengthening**.
In Harpoon this is accomplished by using the ``strengthen`` :ref:`tactic
<cmd-strengthen>`. In a Beluga program, one uses pattern matching together with
an explicit substitution that witnesses the strengthening. Suppose in the below
example that ``x : [g, b : block a1 : unit1, a2 : unit2 |- unit1]``. To
strengthen this, one would use a construction as follows.

.. code-block:: Beluga

    let [g, b : block a1 : unit1, a2 : unit2 |- X[.., b.1]] = x in ...

The synthesized type for ``X`` would be ``g, x1 : unit1 |- unit1``. This is
somewhat confusing because the substitution that witnesses the strengthening
here is in fact a substitution that *weakens* ``X``.

Beluga's subordination analysis over the loaded signature accounts for
transitive dependencies between LF declarations. Beluga will consider
strengthening notably during coverage checking as well as when synthesizing the
type of unknowns, written as ``_`` in LF terms.
