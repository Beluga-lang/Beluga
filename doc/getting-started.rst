Getting Started
===============

Installation
------------

We support only installation on macOS, Linux, and WSL.

Any of the following methods uses ``opam`` 2. Please ensure
that you have that version of ``opam``. You can find the installation
instruction `here <https://opam.ocaml.org/doc/Install.html>`_.

We use recent versions of OCaml, so check which are supported on our
`continuous integration <https://travis-ci.org/github/Beluga-lang/Beluga>`_
before creating an opam switch.
At time of writing, version 4.10.0 is the latest supported version.

.. code-block:: Text

    opam switch create <switch-name> 4.10.0
    opam switch set <switch-name>
    eval $(opam env)

Please replace ``<switch-name>`` with your preferable switch name.

Install using opam
^^^^^^^^^^^^^^^^^^

The following command will install ``beluga`` under the switch you created.

.. code-block:: Text

    opam install beluga

Now ``beluga`` and ``harpoon`` binaries are installed in ``$OPAM_SWITCH_PREFIX/bin``,
and these command work:

.. code-block:: Text

    beluga --help
    harpoon --help

Install from the source
^^^^^^^^^^^^^^^^^^^^^^^

First, clone the repository.

.. code-block:: Text

    git clone https://github.com/Beluga-lang/Beluga
    cd Beluga

Now, build the source with the following commands:

.. code-block:: Text

    opam install --deps-only .
    make

This will place ``beluga`` and ``harpoon`` binaries in the ``bin``
subdirectory. They can be copied wherever you like, or you can add this
subdirectory to your PATH.

Harpoon Example
---------------

You can try the following example to check Harpoon works:

.. code-block:: Beluga

    LF tp : type =
      | i : tp
      | arr : tp -> tp -> tp
    ;

    LF eq : tp -> tp -> type =
      | eq_i : eq i i
      | eq_arr : eq A1 A2 -> eq B1 B2 -> eq (arr A1 B1) (arr A2 B2)
    ;

First, save this code as a file ``tp-refl.bel``. Next, run the following command to load the Harpoon session.

.. code-block:: Text

    harpoon --sig tp-refl.bel

Here, ``--sig`` option represents a *signature* used for proofs. Now, Harpoon will print a session wizard:

.. code-block:: Text

    ## Type Reconstruction begin: tp-refl.bel ##
    ## Type Reconstruction done:  tp-refl.bel ##
    Configuring theorem #1
      Name of theorem (:quit or empty to finish):

The session wizard will ask for the name of theorem, the actual statement, and the induction order. After giving ``tp-refl``, ``{A : [|- tp]} [|- eq A A]``, and ``1``, the session wizard will print this:

.. code-block:: Text

    ## Type Reconstruction begin: stlc.bel ##
    ## Type Reconstruction done:  stlc.bel ##
    Configuring theorem #1
      Name of theorem (:quit or empty to finish): halts_step
      Statement of theorem: [|- step M M'] -> [|- halts M'] -> [|- halts M]
      Induction order (empty for none): 
    Configuring theorem #2
      Name of theorem (:quit or empty to finish): 

Users can give any numbers of theorems they want. Here, for the purpose of this example, we will finish the session wizard, by typing the enter key. Then, Harpoon will display an interactive session:

.. code-block:: Text

    Assumptions
      Meta-assumptions:
        A : ( |- tp)
    are automatically introduced for the subgoal of type
      {A : ( |- tp)} [ |- eq A A]


    Theorem: tp-refl
    intros
    Meta-context:
      A : ( |- tp)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq A A]

    > 

Now we can use interactive tactics to prove the goal (the type under the line). First, by applying ``split [|- A]``, we split the type into cases.

.. code-block:: Text

    Theorem: tp-refl
    intros
    Meta-context:
      A : ( |- tp)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq A A]

    > split [|- A]

This will generate two subgoals, and you will notice that the label (the string on the second line) is changed so that we can see which subgoal we are in.

.. code-block:: Text

    Theorem: tp-refl
    intros <- split [ |- X1] (case arr)
    Meta-context:
      X : ( |- tp)
      X1 : ( |- tp)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq (arr X X1) (arr X X1)]

    >

To prove this, we need ``[|- eq X X]`` and ``[|- eq X1 X1]``. We can get these by induction.

.. code-block:: Text

    Theorem: tp-refl
    intros <- split [ |- X1] (case arr)
    Meta-context:
      X : ( |- tp)
      X1 : ( |- tp)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq (arr X X1) (arr X X1)]

    > by tp-refl [|- X] as EQ_X unboxed

.. code-block:: Text

    Theorem: tp-refl
    intros <- split [ |- X1] (case arr)
    Meta-context:
      X : ( |- tp)
      X1 : ( |- tp)
      EQ_X : ( |- eq X X)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq (arr X X1) (arr X X1)]

    > by tp-refl [|- X1] as EQ_X1 unboxed

With these two, we are able to use ``eq_arr``. 

.. code-block:: Text

    Theorem: tp-refl
    intros <- split [ |- X1] (case arr)
    Meta-context:
      X : ( |- tp)
      X1 : ( |- tp)
      EQ_X : ( |- eq X X)
      EQ_X1 : ( |- eq X1 X1)
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq (arr X X1) (arr X X1)]

    > solve [|- eq_arr EQ_X EQ_X1]

This will solve the subgoal, and Harpoon will subsequently show the next case, which can be solved directly with ``eq_i``.

.. code-block:: Text

    Theorem: tp-refl
    intros <- split [ |- FREE MVar 1] (case i)
    Meta-context:
      
    Computational context:
      

    --------------------------------------------------------------------------------
    [ |- eq i i]

    > solve [|- eq_i]

After solving all subgoals, Harpoon will print the proof script as well as its translation as a Beluga program, and save the proof script (You can check it by ``cat tp-refl.bel``) and type-check the signature file again.

.. code-block:: Text

    Subproof complete! (No subgoals left.)
    Full proof script:
      intros
      { A : ( |- tp)
      | 
      ; split [ |- A] as
        case arr:
        { X : ( |- tp), X1 : ( |- tp)
        | 
        ; by tp-refl [ |- X] as EQ_Y unboxed;
          by tp-refl [ |- X1] as EQ_X unboxed;
          solve [ |- eq_arr EQ_Y EQ_X]
        }
        case i:
        { 
        | 
        ; solve [ |- eq_i]
        }
      }
    Translation generated program:
      mlam A =>
      case [ |- A] of
      | [ |- arr X X1] =>
        let [ |- EQ_Y] = tp-refl [ |- X] in
        let [ |- EQ_X] = tp-refl [ |- X1] in [ |- eq_arr EQ_Y EQ_X]
      | [ |- i] =>
        [ |- eq_i]

    No theorems left. Checking translated proofs.
    - Translated proofs successfully checked.
    Proof complete! (No theorems left.)
    ## Type Reconstruction begin: t/harpoon/tp-refl.bel ##
    ## Type Reconstruction done:  t/harpoon/tp-refl.bel ##

Once the proof is completed, Harpoon will restart the session wizard, and we can choose whether to prove more theorems or ``:quit``.

.. code-block:: Text

    Configuring theorem #1
      Name of theorem (:quit or empty to finish): :quit
    Harpoon terminated.

That's it! If you want to know more details including how to write the signature file and what kinds of tactics do we provide, please read the :ref:`common elements <common>` and :ref:`interactive proving with harpoon <harpoon>` section of this page. For additional examples, you can check out `the test directory <https://github.com/Beluga-lang/Beluga/tree/master/t>`_ in `our github repository <https://github.com/Beluga-lang/Beluga>`_.
