These are some remarks that didn't make it into the Twelf source files.



   * I unfortunately named everything for store typings using the base name
     "store", which might lead the reader to mistake them for heap-related
     items. Heap-related items are named using a base name of "heap". (-:



   * The definitions you see here actually went through several revisions,
     at least a few of which were inspired by taking a look at Rob Simmons
     (senior?) thesis after banging my head on the wall for a bit. (-: What
     you see here is the result of one (well-known) principle I think: keep
     it simple stupid. As a corollary, functions should be defined such that
     they're obviously functions, i.e., such that they pass the uniqueness
     checker.



   * Consider my original version of can_step.

        can_step :
           progresses S E
           <- ({H:heap N} wt_heap S H -> step H E H' E').

     So, Twelf is going to quantify H' and E' at the top-level of can_step.
     Thus, it says E progresses with respect to a store typing S if there
     are some H' and E' such that for all heaps H that are well-typed with
     respect to S, (step H E H' E') holds. This is pretty clearly bogus. In
     fact, I think this was partly indicated by the "parameter dependency"
     error I was getting at one point.
