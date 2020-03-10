.. _LF:

The Logical Framework LF
========================

Languages are encoded for study in Beluga using the Logical Framework LF [1]_.
New syntactic categories are defined using the ``LF`` toplevel definition, which
defines a new LF (indexed) type together with its constructors.

Basic example: natural numbers
------------------------------

.. code-block:: Beluga

    LF nat : type =
      | zero : nat
      | succ : nat -> nat
    ;

The first line defines a new simple LF type ``nat`` and the following lines
define its constructors, ``zero`` and ``succ``. The number three is written
``succ (succ (succ zero))`` in this encoding.

HOAS example: lambda calculus
-----------------------------

Beluga is a domain-specific language for reasoning about formal systems, and one
of the simplest such systems is the lambda calculus. Unlike in the natural
numbers, lambda-terms contain *binders*. The philosophy of LF is to represent
binders using higher-order abstract syntax (HOAS). That is, the functions
of the metalanguage (LF) are used to represent the binding structure of the
object-language (lambda calculus). Here is how we define untyped lambda terms
using HOAS.

.. code-block:: Beluga

    LF tm : type =
      | lam : (tm -> tm) -> tm
      | app : tm -> tm -> tm
    ;

.. note:
   The astute reader might observe that the type ``tm`` appears in the
   definition of ``lam`` in a *negative position*, on the left of an arrow. This
   is not a problem in LF as the function space is merely representational:
   pattern matching and recursion are not a part of LF. This function space can
   be used only to represent binding structure.

One immense benefit of HOAS is that the object-language inherits the
substitution properties of the metalanguage. In practice, this means that one
needs not define substitution, but rather simply use LF function
application. For example, consider the following encoding of a small-step,
call-by-name operational semantics for the lambda calculus.

.. code-block:: Beluga

   LF step : tm -> tm -> type =
     | e_app : step M M' ->
               % -----------------------
               step (app M N) (app M' N)

     | beta : step (app (lam \x. M) N) (M N)
   ;

First, observe that ``step`` is not a simple type. It is indexed by two terms,
so we understand it as a binary relation between terms.

Second, observe the presence of *free variables* ``M``, ``M'``, and ``N``. Any
free variable is automatically Pi-quantified at the very front of the
constructor being defined. Thus, the internal type of ``e_app`` is really ``{M :
tm} {M' : tm} {N : tm} step M M' -> step (app M N) (app M' N)``.
(Beluga uses curly braces to write Pi-types.)
We call such automatically quantified variables *implicit parameters*.
The types of implicit parameters are determined by type reconstruction, and it
is not possible for the user to explicitly provide an instantiation for an
implicit parameter.

Next, the rule ``e_app`` has been suggestively written with a commented line to
illustrate that one would ordinarily write this as an inference rule. In Beluga,
we use ``LF`` declarations to uniformly represent the syntax and the inference
rules of object languages.

Finally, the rule ``beta`` demonstrates HOAS in action. We use LF function
application to implement the beta reduction of the lambda calculus.

To complete the example encoding of the lambda calculus, we will now turn our
attention to a simple type assignment system for this language. First, we will
define the syntax of types.

.. code-block:: Beluga

    LF tp : type =
      | base : tp
      | arr : tp -> tp -> tp
    ;

Second, we define the typing judgment as an indexed type.
In this case, we understand ``oft`` as relating a term ``tm`` to a type ``tp``.

.. code-block:: Beluga

    LF oft : tm -> tp -> type =
      | t_app : oft M (arr A B) -> oft N A ->
                % ---------------------------
                oft (app M N) B

      | t_lam : ({x : tm} oft x A -> oft (M x) B) ->
                % ----------------------------------
                oft (lam (\x. M)) (arr A B)
    ;

We will concentrate on the rule ``t_lam``. Here, the variable ``M`` is
understood as the body of the lambda-abstraction, and it depends on a parameter
``x``. The premise of this rule reads "for any term ``x``, if ``x`` is of type
``A``, then ``M x`` is of type ``B``". This precisely captures the parametric
reasoning used on paper when proving that a lambda-abstract has an arrow-type.
Here it is necessary to explicitly write a Pi-type for ``x`` as leaving it
implicit would have it incorrect quantified at the level above.

To *reason* about these definitions, one would formulate a theorem and prove it,
either by writing a :ref:`functional program in Beluga <beluga>` or
:ref:`interactively with Harpoon <harpoon>`.

.. [1] TODO cite LF paper
