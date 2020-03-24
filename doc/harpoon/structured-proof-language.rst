.. _structured proof language:

Structured Proof Script Language
================================

Harpoon proofs are recorded in signature files as a **proof script**. This is a
structured language whose core constructs close resembles the syntax of
:ref:`proof tactics`. In a signature file, a proof named ``foo`` is declared as
follows.

.. code-block:: Beluga

    proof foo : tau = P;

where ``tau`` is a :ref:`computation type <computation types>` and ``P`` is the body of the proof.
