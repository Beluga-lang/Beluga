.. _contextual lf:

Contextual LF
=============

In contrast with languages such as Coq or Agda that feature full dependent
types, Beluga has an *indexed type system*. This is a restricted form of
dependent types in which one quantifies only over a specific *index
domain*. The index domain of Beluga is Contextual LF.

At a high level, a Contextual LF object (or type) is an LF term (or type)
together with an LF context in which the term (or type) makes sense.
For example, consider the following syntax of types for the simply-typed lambda
calculus together with a structural equality relation on types.

.. code-block:: Beluga

    LF tp : type =
      | base : tp
      | arr : tp -> tp -> tp
    ;

    LF eq : tp -> tp -> type =
      | eq_base : eq base base
      | eq_arr : eq A1 A2 -> eq B1 B2 ->
                 % ------------------------
                 eq (arr A1 B1) (arr A2 B2)
    ;

The contextual object that encodes a closed proof that the ``base`` type is
equal to the ``base`` type is ``|- eq_base``. We write this sometimes with
parentheses to make reading easier, e.g. ``( |- eq_base )``.

Open terms can be represented by using a nonempty LF context. For example,

.. code-block:: Beluga

    x : eq A B |- eq_arr x eq_base

is a contextual object of type ``x : eq A B |- eq (arr A base) (arr B base)``.

.. _computation types:

Computation types
-----------------

Contextual LF objects and types may be *boxed* into **computation types**. These
types are primarily used for encoding theorems about a formal system.
For example, the type of a theorem expressing that equality is reflexive would
be

.. code-block:: Beluga

    {A : |- tp} [ |- eq A A]

We read this as "for all (closed) types ``A`` , ``A`` is equal to itself."
This is a **computation type**. It is composed of two parts in this example: a
*PiBox-type* and a *box-type*. The PiBox is used as a quantifier; we will go
into more depth on this in the following section.
The syntax ``[ |- eq A A ]`` is a *boxed contextual type*: any contextual type may
be surrounded by a box ``[ ]`` to embed it as a base computation type.
Similarly, contextual objects may be boxed to form computation expressions.

Another example theorem ``trans``, that equality is transitive, can be expressed
as

.. code-block:: Beluga

    [ |- eq A B] -> [ |- eq B C] -> [ |- eq A C]

Similar to in a pure LF type (see :ref:`here <free variables>`), free metavariables
appearing in a computation type are automatically abstracted over using PiBox at
the front. So really, the above example type is elaborated into

.. code-block:: Beluga

    {A : |- tp} {B : |- tp} {C : |- tp}
    [ |- eq A B] -> [ |- eq B C] -> [ |- eq A C]

But again as in a pure LF type, these quantifiers are implicit and there is no
way for a programmer to explicitly supply an instantiation for them. The
instantiations are found when the theorem ``trans`` is used.

This example illustrates the simple function space, written with the arrow
``->``. In Beluga, the dependent function space (using the PiBox syntax)
is separate from the simple function space (using the arrow syntax).

To recap, the formal grammar of computation types is the following.

.. code-block::

    Types T ::= B | [U] | T1 -> T2 | {X : U} T

where ``B`` denotes an :ref:`inductive type <inductive types>` and ``U`` denotes a
contextual type. The remaining two forms are the simple and dependent function
space, respectively.

Metavariables
-------------

The syntax ``{A : |- tp} ...`` expresses what's called a PiBox-type. This
example quantifies over the contextual type ``|- tp`` and binds ``A`` as a
**metavariable**. Whenever a metavariable is used, as ``A`` is used for example
in ``eq A A``, it is given a *substitution*. This substitution mediates between
the LF context of the metavariable and the LF context at the use site. If no
explicit substitution is provided, an identity substitution is assumed. An
identity substitution is sufficient in the example because the context of both
the metavariable and its use site is the empty context.

For example, suppose we have the metavariable ``X : (x : tm, y : tm |-
tp)``. (Perhaps ``X`` refers to ``x, y |- arr x y``.) Then, ``X[base, base] : |-
tp``. Here we use an explicit substitution to instantiate the bound variables
``x`` and ``y``.

Context variables and schemas
-----------------------------

Beluga provides a mechanism for abstracting over and quantifying over
contexts. An abstract context is referred to by a **context variable**. A context
variable is a special form of metavariable.

Whereas kinds classify types, contexts are classified by **schemas**. A
schema essentially lists the possible types of the variables occurring in the
context. The following declaration defines a schema ``ctx`` that can contain
only types.

.. code-block:: Beluga

    schema ctx = tp;

Before we can elaborate an example demonstrating context variables, first
consider the following syntax of terms for the simply typed lambda calculus as
well as a typing judgment for this language.

.. code-block:: Beluga

    LF tm : type =
      | app : tm -> tm -> tm
      | lam : tp -> (tm -> tm) -> tm
    ;

    LF oft : tm -> tp -> type =
      | t_app : oft M (arr A B) -> oft N A ->
                % ---------------------------
                oft (app M N) B

      | t_lam : ({x : tm} oft x A -> oft (M x) B) ->
                % ----------------------------------
                oft (lam A M) (arr A B)


This syntax of terms includes a type annotation on lambda abstractions, and the
typing judgment ensures that it is the type given in the annotation that is used
as the parameter ``x``'s type in the premise of the ``t_lam`` rule.

This language admits *type uniqueness*. That is, given two
typing derivations for the same term, the types assigned to that term must be
equal. We can state this theorem as a computation type in Beluga as follows.

.. code-block:: Beluga

    (g : ctx) [g |- oft M A1[]] -> [g |- oft M A2[]] -> [|- eq A1 A2]

First, notice the syntax ``(g : ctx) ...``. This is called *implicit context
quantification*.
Unlike for ordinary implicit metavariables such as ``M``, the
schema of an implicit context variable cannot be inferred by type
reconstruction. Therefore, one must use implicit context quantification to
explicitly specify the schema of the context variable.

Second, notice that the metavariables ``A1`` and ``A2``, referring to types, are
associated with the substitution ``[]`` in the assumptions of the theorem. Type
reconstruction is in some sense a greedy algorithm, so had these substitutions
been left out, the type of ``A1``, upon appearing in ``g |- oft M A1``, would be
``g |- tp``. But this makes no sense because types ought to be *closed* in the
simply-typed lambda calculus. To specify that the metavariables ``A1`` and
``A2`` must be closed, we associate them with a *weakening substitution*
``[]``. This way, type reconstruction will correct infer that the context of
these metavariables is empty.

Confusingly, the reported error had the weakening substitutions been omitted
would be relating to the occurrences of ``A1`` and ``A2`` in ``|- eq A1
A2``. Here, the implicit identity substitution would be ill-typed. Recall that
the type of ``A1``, for instance, would have been inferred as ``g |- tp`` and
the identity subsitution would need to send the metavariable's context ``g`` to
the empty context, which it does not. In general, when dealing with ill-typed
substitution errors, it is worth paying close attention to *every* occurrence of
any relevant metavariables.

Unboxing
--------

When one has a computational variable referring of a boxed contextual type, one
frequently likes to promote this variable to a metavariable. This process is
called *unboxing*.
For example, suppose we have the assumption ``x : [|- tp]``.

* In Beluga, one writes ``let [_ |- X] = x in ...`` in order to unbox ``x`` as the
  metavariable ``X``.
* In Harpoon, one uses the ``unbox`` :ref:`tactic <cmd-unbox>` for this: ``unbox x as X``.
