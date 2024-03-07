# Overview

This artifact contains the Beluga mechanization for the paper

    Mechanizing Session-Types Using a Structural View
    C. Sano, R. Kavanagh, B. Pientka
    Proceedings of the ACM on Programming Languages, Volume 7,
    Number OOPSLA2, Article No. 235 (October 2023),
    https://doi.org/10.1145/3622810

and is a copy of the accompanying artifact (https://doi.org/10.5281/zenodo.8329645)

Below are files that are included in this artifact.

	cp.cfg         - Collects all used Beluga source files
	cp_base.bel    - Contains encodings of session types and processes
	cp_linear.bel  - Contains encoding of the linearity predicate
	cp_statics.bel - Contains encoding of the type judgment
	cp_dyn.bel     - Contains encoding of the reductions and congruences
	cp_lemmas.bel  - Contains proofs of intermediary lemmas
	cp_thrm.bel    - Proof of type preservation

There are some minor differences in code snippets as written in the
paper for presentation purposes compared to the code in the artifact,
which we summarize below.

| Item                    | On-paper Notation | Artifact     |
|-------------------------|-------------------|--------------|
| Reduction rule names    | βcut1 and βinl    | β∥1 and β⊕&1 |
| Structural Equivalences | equiv P Q         | P ≡ Q        |
| Reductions              | step P Q          | P ⇛ Q        |
| Abstractions            | λx. M             | \x. M        |

## Paper to Artifact Table

| Definition/Proofs                                     | Paper                        | File           | Definition Name                                    |
|-------------------------------------------------------|------------------------------|----------------|----------------------------------------------------|
| Session types, duality, and processes                 | Sections 4.1 and 4.2         | cp_base.bel    | tp, dual, and proc                                 |
| Linearity predicate                                   | Section 4.3                  | cp_linear.bel  | linear                                             |
| Type judgments                                        | Section 4.4                  | cp_statics.bel | wtp                                                |
| Reductions and Structural Equivalences                | Section 4.5                  | cp_dyn.bel     | ⇛ and ≡ (used as infix operators)                  |
| Symmetricity and Uniqueness of dual                   | Section 6.1                  | cp_lemmas.bel  | dual_sym and dual_uniq                             |
| Strengthening Lemmas                                  | Section 6.2, Lemma 6.1 (1-5) | cp_lemmas.bel  | str_hyp, str_lin, str_wtp, str_step, and str_equiv |
| Linearity implies usage                               | Section 6.3, Lemma 6.2       | cp_lemmas.bel  | lin_name_must_appear                               |
| Structural equivalence preserves linearity and typing | Section 6.3, Lemma 6.3       | cp_thrm.bel    | lin_s≡ and wtp_s≡                                  |
| Type preservation                                     | Section 6.4, Theorem 6.4     | cp_thrm.bel    | lin_s and wtp_s                                    |


# Installation and Execution

This mechanization is compatible with Beluga version 1.1.

## Installation

The easiest way to install Beluga is using `opam`:

    >> opam install beluga.1.1

Beluga can also be installed from source by following the "Installation
from the source" instructions on
https://github.com/Beluga-lang/Beluga/tree/v1.1

Alternatively, we have provided a virtual machine based on OpenBSD 7.3
that has Beluga 1.1, its sources, and our mechanization pre-installed.
This QCOW2 disk image can be run using QEMU using the command:

    >> qemu-system-amd64 -hda artifact.qcow2 -m 1G

For a better user experience, we suggest the following options, which
give the virtual machine 4 gigabytes of memory, four CPUs, and allow
the machine to be accessed over SSH on localhost port 60022 using
username `artifact` and password `artifact`:

    >> qemu-system-amd64 -hda artifact.qcow2 -m 4G -smp 4 \
                         -nic user,hostfwd=tcp::60022-:22
    >> ssh artifact@127.0.0.1 -p 60022

## Execution

Once Beluga is installed, it can be run on the file `cp.cfg`. The
following is the expected output:

	>> beluga cp.cfg
	## Type Reconstruction begin: ./cp_base.bel ##
	## Type Reconstruction done:  ./cp_base.bel ##
	## Type Reconstruction begin: ./cp_linear.bel ##
	## Type Reconstruction done:  ./cp_linear.bel ##
	## Type Reconstruction begin: ./cp_statics.bel ##
	## Type Reconstruction done:  ./cp_statics.bel ##
	## Type Reconstruction begin: ./cp_dyn.bel ##
	## Type Reconstruction done:  ./cp_dyn.bel ##
	## Type Reconstruction begin: ./cp_lemmas.bel ##
	## Type Reconstruction done:  ./cp_lemmas.bel ##
	## Type Reconstruction begin: ./cp_thrm.bel ##
	## Type Reconstruction done:  ./cp_thrm.bel ##
