.. _index:

Beluga/Harpoon user's manual
============================

Beluga is a language for encoding and reasoning about formal systems specified
by inference rules, e.g. lambda calculi and type systems. It uses contextual
modal logic as its foundation.
Object-language binding constructs are encoded using higher-order abstract
syntax. That is, functions are used to encode binders.
Terms are paired with the contexts in which they are meaningful to form
*contextual objects*, enabling reasoning about open terms.
Proofs in Beluga are represented by recursive programs according to the
Curry-Howard correspondence.

Harpoon is an interactive proof development REPL built on top of Beluga. Users
develop proofs by successively eliminating subgoals using a small, fixed set of
tactics. Behind the scenes, the execution of tactics builds a proof script that
can be machine-translated into a traditional Beluga program.

The Beluga project is developed at the Complogic group at McGill university, led
by Professor Brigitte Pientka. It is implemented in OCaml.

.. toctree::
   :maxdepth: 2

   installation
   common/index
   harpoon/index

Funding
-------

This research has been funded through: NSERC (Natural Science and Engineering
Research Council), FQRNT Recherche d'Equipe, PSR-SIIRI Projets conjoints de
recherche et d'innovation and 63e session de la Commission permanente de
coopération franco-québécoise by Ministère du Développement économique, de
l'Innovation et de l'Exportation au Quebec.

:ref:`search`
