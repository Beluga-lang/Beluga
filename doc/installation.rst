Installation
============

We support only installation from source, on macOS and Linux.

First, ensure that you have ``opam`` 2.
Next, clone the repository.

.. code-block:: Text

    git clone https://github.com/Beluga-lang/Beluga
    cd Beluga

We use recent versions of OCaml, so check which are supported on our
`continuous integration <https://travis-ci.org/github/Beluga-lang/Beluga>`_
before creating an opam
switch.
At time of writing, version 4.09.0 is the latest supported version.

.. code-block:: Text

    opam switch create . 4.09.0
    eval $(opam env --set-switch)
    opam install --deps-only .
    make

This will place ``beluga`` and ``harpoon`` binaries in the ``bin``
subdirectory. They can be copied wherever you like, or you can add this
subdirectory to your PATH.
