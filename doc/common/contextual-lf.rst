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

The type of a theorem expressing that equality is reflexive would be

.. code-block:: Beluga

    {A : |- tp} [ |- eq A A]

This is a *computation type*. It stands in contrast with the types seen in
``LF`` declarations, which are *pure LF* types. An LF type, together with a
context, is embedded as a computation type using the box syntax,
e.g. ``[ |- eq A A]`` pairs the empty context (on the left of the turnstile)
with the LF type ``eq A A``.

The syntax ``{A : |- tp} ...`` expresses a Pi-type. This example quantifies over
the contextual type ``|- tp`` and binds ``A`` as a *metavariable*. Whenever a
metavariable is used, as ``A`` is used for example in ``eq A A``, it is
given a *substitution*. This substitution mediates between the context of the
metavariable and the context at the use site. If no explicit substitution is
provided, an identity substitution is assumed. An identity substitution is
sufficient in the example because the context of both the metavariable and its
use site is the empty context.

For example, suppose we have the metavariable ``X : (x : tm, y : tm |-
tp)``. (Perhaps ``X`` refers to ``x, y |- arr x y``.) Then, ``X[base, base] : |-
tp``. Here we use an explicit substitution to instantiate the bound variables
``x`` and ``y``.

Context variables
-----------------

Beluga provides a mechanism for abstracting over and quantifying over
contexts. An abstract context is referred to by a *context variable*. A context
variable is a special form of metavariable.

Whereas kinds classify types, contexts are classified by *schemas*. A
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
                oft (lam A \x. M) (arr A B)


This syntax of terms includes a type annotation on lambda abstractions, and the
typing judgment ensures that it is the type given in the annotation that is used
as the parameter ``x``'s type in the premise of the ``t_lam`` rule.

For this language, one can prove *type uniqueness*. That is, given two
typing derivations for the same term, the types assigned to that term must be
equal. We can state this theorem as a computation type in Beluga as follows.

.. code-block:: Beluga

    (g : ctx) [g |- oft M A1[]] -> [g |- oft M A2[]] -> [|- eq A1 A2]

First, notice the syntax ``(g : ctx) ...``. This is called implicit context
quantification. Unlike for ordinary implicit metavariables such as ``M``, the
schema of an implicit context variable cannot be inferred by type
reconstruction. Therefore, one must use implicit context quantification to
explicitly specify the schema of the context variable.

Second, notice that the metavariables ``A1`` and ``A2``, referring to types, are
associated with the substitution ``[]`` in the assumptions of the theorem. Type
reconstruction is in some sense a greedy algorithm, so had these substitutions
been left out, the of ``A1``, upon appearing as in ``g |- oft M A1``, would be
``g |- tp``. But this makes no sense because types ought to be *closed* in the
simply-typed lambda calculus. To specify that the metavariables ``A1`` and
``A2`` must be closed, we associate them with a *weakening substitution* ``[]``.

Confusingly, the reported error had the weakening substitutions been omitted
would be relating to the occurrences of ``A1`` and ``A2`` in ``|- eq A1
A2``. Here, the implicit identity substitution would be ill-typed. The type of
``A1``, for instance, would be ``g |- tp`` and identity subsitution would
need to send the context ``g`` to the empty context.

Unboxing
--------

When one has a computational variable referring of a boxed contextual type, one
frequently likes to promote this variable to a metavariable. This process is
called *unboxing*.
For example, suppose we have the assumption ``x : [|- tp]``.

* In Beluga, one writes ``let [_ |- X] = x in ...`` in order to unbox ``x`` as the
  metavariable ``X``.
* In Harpoon, one uses the ``unbox`` tactic for this: ``unbox x as X``.
