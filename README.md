## [Beluga](http://complogic.cs.mcgill.ca/beluga/ "Beluga home page")  [![Build & Test](https://github.com/Beluga-lang/Beluga/actions/workflows/build-and-test.yml/badge.svg)](https://github.com/Beluga-lang/Beluga/actions/workflows/build-and-test.yml)

[Beluga](http://complogic.cs.mcgill.ca/beluga/ "Beluga home page") is a functional programming language designed for reasoning about formal systems.
It features direct support for object-level binding constructs using higher order abstract syntax and treats contexts as first class objects.

## Getting started

### Prerequisites

Install the OCaml package manager ([opam](http://opam.ocaml.org/)) by following the instructions at <http://opam.ocaml.org/doc/Install.html>.

Optionally, [`rlwrap`](https://github.com/hanslub42/rlwrap) may be installed to greatly improve the Beluga interactive mode user experience.

### Installation from the opam repository

Beluga may be installed in the current opam switch using:

```bash
opam install beluga
eval $(opam env)
```

Alternatively, an opam switch may be created specifically for Beluga using:

```bash
mkdir Beluga
cd Beluga
opam switch create . --empty
opam install beluga
eval $(opam env)
```

You can now run Beluga programs using the `beluga` executable:

```bash
beluga path/to/program.bel
```

### Installation from the source

To build Beluga from the source code and install it in its own opam switch:

```bash
git clone https://github.com/Beluga-lang/Beluga.git Beluga
cd Beluga
opam switch create . --empty
opam install .
```

The `beluga` executable is then accessible from the newly created opam switch.

### Development

To start working on Beluga, clone the repository and create an opam switch with the dependencies installed:

```bash
git clone https://github.com/Beluga-lang/Beluga.git Beluga
cd Beluga
opam switch create . --deps-only --with-test --yes
eval $(opam env)
```

Use `make` to compile, `make test` to compile and run the tests, and `make clean` to clean the directory of compilation results.
Use `./LINT` to find code style errors.

To use any of the compiled executables as if they were installed from opam, use `dune exec [executable]`.
For instance, you can run Beluga programs using the compiled development version of `beluga` using:

```bash
dune exec beluga path/to/program.bel
```

You can run a Harpoon session using the compiled development version of `harpoon` using:

```bash
dune exec harpoon -- --sig path/to/program.bel
```

See the [`MakeFile`](./MakeFile) for other available development commands.

## Interactive Mode

For interactive proofs, we recommend using [Harpoon](https://beluga-lang.readthedocs.io/en/latest/harpoon/index.html).
A detailed list of commands and tactics is available [here](https://beluga-lang.readthedocs.io/en/latest/harpoon/interactive-reference.html).

## Beluga-mode for GNU Emacs

Beluga includes a major mode for programming in Emacs.
The elisp file is located in the [tools](./tools) directory.
To configure Beluga-mode:

1. Update your `~/.emacs` or `~/.emacs.d/init.el` file with the lines written below.
   XEmacs users must update `~/.emacs` or `~/.xemacs/init.el` with the same text.
   Create any of these files if they do not exist already.
   * You should replace `path/to/beluga` with the actual path of the Beluga directory.
     ```
     (add-to-list 'load-path "path/to/beluga/tools/")
     (load "beluga-mode.el")
     ```
   * NOTE: Feel free to move the beluga-mode.el file to another directory so long as you add its location to the Emacs load-path.

2. Restart Emacs.
   Emacs will now launch in Beluga-mode automatically when you open a Beluga program.
