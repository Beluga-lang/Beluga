To be able to parse annotated proofs, we first need to retrieve the annotated expchk corresponding to each function in the source file.
For this purpose, we have a table in LatexRec called annotatedProofs. In RecSgn, (name, e_ann) pairs are added to this table.

We have another table called recTypes in LatexRec that we fill with functions from the Store and their corresponding e_ann that we have stored in annotatedProofs. 
For every function in the Store, we add a binding to our RecTypes table.


BUG 1) 

Beluga/examples/unique/unique.bel  (source file contains 1 lemma without contexts + 3 theorem proofs with contexts)

we have :
- 4 elements in annotatedProofs (as expected)
- 5 functions in Store (why ??)
=> bug in our conversion from annotatedProofs to recTypes because of this

All this gets printed when you run beluga with the +latex flag if you want to take a look.




BUG 2)

Beluga/examples/unique/unique-crec.bel  (source file also contains 1 lemma without contexts + 3 theorem proofs with contexts)

We have 4 elem in annotatedProofs, 4 in the Store and 4 in recTypes, the conversion goes well.

From there, we hit a : DynArray.Invalid_arg error. Once again, if you run the code with +latex flag, all gets printed.
This is a problem with the theorem statements of the theorems with context like :
"rec unique : {g:tctx} {E:[g |- exp]} [g |- type_of E T[]] -> [g |- type_of E T'[]] ->  [ |- eq T T'] ="

To print a theorem, we need to print the for alls, the assumptions and the conclusion : all this is done using functions in LatexInductive. The problem occurs when printing the for alls in Pretty.cdeclToLatex. 
UPDATE :
The problem occurred when printing "for all g:tctx" (corresponding to {g:tctx}) : the schema tctx is not in store at the moment we want to print it. I fixed this problem with a try with statement for the moment.


Now we get all the way to a Latex output for Beluga/examples/unique/unique-crec.bel !
The Latex does not compile yet but it is promising.
The problem is I don't really know how the proof should look like on paper in order to improve the Latex generation.










