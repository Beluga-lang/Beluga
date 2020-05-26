## [Beluga](http://complogic.cs.mcgill.ca/beluga/ "Beluga home page")  [![Build Status](https://travis-ci.org/Beluga-lang/Beluga.svg?branch=master)](https://travis-ci.org/Beluga-lang/Beluga)

[Beluga](http://complogic.cs.mcgill.ca/beluga/ "Beluga home page") is a functional programming language designed for reasoning
about formal systems. It features direct support for object-level
binding constructs using higher order abstract syntax and treats
contexts as first class objects.


## Installation & Configuration Guide
<!-- ------------------- -->

The following packages must be installed to use Beluga:

* opam                     <http://opam.ocaml.org/doc/Install.html>
* ocaml 4.05.0+:           <http://caml.inria.fr/download.en.html>
* extlib:                  <http://code.google.com/p/ocaml-extlib/downloads/list>
* gen:                     <https://github.com/c-cube/gen>
* linenoise:               <https://github.com/ocaml-community/ocaml-linenoise>
* sedlex:                  <https://github.com/ocaml-community/sedlex>


Optional dependencies (for improved beli mode):

* rlwrap:                  <http://utopia.knoware.nl/~hlub/uck/rlwrap/>


#### General instructions

```bash
$ YOUR_PKG_MNGR install opam
$ opam init --bare
$ opam switch create ocaml-base-compiler.4.09.0
$ eval $(opam env)
# from the Beluga directory
$ opam install --deps-only .
```

The interactive mode is greatly improved if you have rlwrap installed,
so you might also want to consider:

```
$ YOUR_PKG_MNGR install rlwrap
```

## Building


Compile by running "make" from the Beluga directory.
```bash
$ make
```

You can now run Beluga programs with the newly
"beluga" executable in the "bin" directory

```bash
$ ./bin/beluga path/to/program.bel
```

Tip: Running `make clean` will clean the directory of compilation results

## Interactive Mode

For interactive proofs, we recommend using
[Harpoon](https://beluga-lang.readthedocs.io/en/latest/harpoon/index.html).
A detailed list of commands and tactics is available
[here](https://beluga-lang.readthedocs.io/en/latest/harpoon/interactive-reference.html).

## Beluga-mode for GNU Emacs

Beluga includes a major mode for programming in Emacs. The elisp file is
located in the ./tools directory. To configure Beluga-mode:

1. Update your ~/.emacs or ~/.emacs.d/init.el file with the lines written below.
   XEmacs users must update ~/.emacs or ~/.xemacs/init.el with the same text.
   Create any of these files if they do not exist already.
   * You should replace path/to/beluga with the actual path of the Beluga directory.
     (add-to-list 'load-path "path/to/beluga/tools/")
     (load "beluga-mode.el")
   * NOTE: Feel free to move the beluga-mode.el file to another directory so long as
     you add its location to the Emacs load-path.

2. Restart Emacs.
   Emacs will now launch in Beluga-mode automatically when you open a Beluga
   program.
