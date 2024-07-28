# Overview

This artifact contains the Beluga mechanization for the paper

    A Beluga Formalization of the Harmony Lemma in the π-Calculus
    Gabriele Cecilia and Alberto Momigliano
    Proceedings Workshop on LFMTP 2024, Tallinn, Estonia, 8th July 2024,
    Electronic Proceedings in Theoretical Computer Science 404, pp. 1-17
    https://doi.org/10.4204/EPTCS.404.1

and it contains the code of [this original repository](https://github.com/GabrieleCecilia/concurrent-benchmark-solution/). This work provides a Beluga solution to the 2nd challenge of the Concurrent Calculi Formalisation Benchmark ([CCFB](https://concurrentbenchmark.github.io/)).

Below are files that are included in this artifact.

	all.cfg                      - Collects all used Beluga source files
	1_definitions.bel            - Contains encoding of syntax and semantics of the pi-calculus
	2_input_rewriting.bel,       - Contain proofs of rewriting lemmas for specific transitions
	3_free_output_rewriting.bel,
	4_bound_output_rewriting.bel 
	5_theorem1.bel               - Proof of the first implication of the Harmony Lemma
	6_stepcong_lemma.bel         - Contains proofs of a congruence-as-bisimilarity and a strengthening lemma 
	7_reduction_rewriting.bel    - Contains proof of a rewriting lemma for reductions
	8_theorem2.bel               - Proof of the second implication of the Harmony Lemma



## Paper to Artifact Table

| Definition/Proofs                             | Paper         | File                         | Definition Name                           |
|-----------------------------------------------|---------------|------------------------------|-------------------------------------------|
| Names, processes                              | Section 3.1   | 1_definitions.bel            | names, proc                               |
| Congruence, reduction                         | Section 3.2   | 1_definitions.bel            | cong, red                                 |
| Actions, transitions                          | Section 3.3   | 1_definitions.bel            | f_act, b_act, f_step, b_step              |
| Rewriting lemma for input transitions         | Section 3.4.1 | 2_input_rewriting.bel        | bs_in_rew                                 |
| Rewriting lemma for free output transitions   | Section 3.4.1 | 3_free_output_rewriting.bel  | fs_out_rew                                |
| Rewriting lemma for bound output transitions  | Section 3.4.1 | 4_bound_output_rewriting.bel | bs_out_rew                                |
| Theorem 1 (1st Harmony Lemma implication)     | Section 3.4.1 | 5_theorem1.bel               | fstep_impl_red                            |
| Strengthening lemma                           | Section 3.4.2 | 6_stepcong_lemma.bel         | strengthen_fstep, strengthen_bstep        |
| Congruence-as-bisimilarity lemma              | Section 3.4.2 | 6_stepcong_lemma.bel         | cong_fstepleft_impl_fstepright, cong_fstepright_impl_fstepleft, cong_bstepright_impl_bstepleft, cong_fstepleft_impl_fstepright |
| Rewriting lemma for reductions                | Section 3.4.2 | 7_reduction_rewriting.bel    | red_impl_red_rew                          |
| Theorem 2 (2nd Harmony Lemma implication)     | Section 3.4.2 | 8_theorem2.bel               | red_impl_fstepcong                        |


# Execution

This mechanization is compatible with Beluga version 1.1.1.

Once Beluga is installed, it can be run on the file `all.cfg`. The
following is the expected output:

	>> beluga all.cfg
	## Type Reconstruction begin: ./1_definitions.bel ##
	## Type Reconstruction done:  ./1_definitions.bel ##
	## Type Reconstruction begin: ./2_input_rewriting.bel ##
	## Type Reconstruction done:  ./2_input_rewriting.bel ##
	## Type Reconstruction begin: ./3_free_output_rewriting.bel ##
	## Type Reconstruction done:  ./3_free_output_rewriting.bel ##
	## Type Reconstruction begin: ./4_bound_output_rewriting.bel ##
	## Type Reconstruction done:  ./4_bound_output_rewriting.bel ##
	## Type Reconstruction begin: ./5_theorem1.bel ##
	## Type Reconstruction done:  ./5_theorem1.bel ##
	## Type Reconstruction begin: ./6_stepcong_lemma.bel ##
	## Type Reconstruction done:  ./6_stepcong_lemma.bel ##
	## Type Reconstruction begin: ./7_reduction_rewriting.bel ##
	## Type Reconstruction done:  ./7_reduction_rewriting.bel ##
	## Type Reconstruction begin: ./8_theorem2.bel ##
	## Type Reconstruction done:  ./8_theorem2.bel ##

