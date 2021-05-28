(** Contextual type-based name generator.
    This name generator will use programmer-supplied naming hints
    (falling back to good old X, Y, Z) but adjust the numeric counter
    on the name so it is the smallest allowed in a given context.

    This name generation strategy notably does not use any global
    counters, so its results are independent of order of operations.
    The result of this generator depends only on what ambient context
    of names is passed as input.

    The general idiom to use this generator is:
        NameGen.(var tau |> renumber names)
    where
        names : Id.name list
    can be calculated using helper functions from context.ml.
    (See the names_of_Xctx family of functions.)

    Caveats.
    1. In general you need to be conscious of when you calculate
       name lists, as this does incur a traversal of the context.
    2. This name generation strategy is strictly less
       efficient than global variable-based strategies, as the
       `renumber` function -- the core algorithm of this module --
       traverses the entire name list to decide what number to assign
       the input name.

    As for point 2, a more efficient data structure for representing
    the name list could improve efficiency substantially. In
    particular, a hashtable or a trie that associates to each name its
    highest count.
 *)
open Syntax
open Syntax.Int

(** Generates a raw parameter variable name for a given LF type.
    Uses the programmer-supplied name hint, with a fallback.
 *)
val pvar : LF.typ -> Id.name

(** Generates a raw bound variable name for a given LF type.
    Uses the programmer-supplied name hint, with a fallback.
 *)
val bvar : LF.typ -> Id.name

(** Generate a raw metavariable name for a given LF type.
    Uses programmer-supplied name hints with a fallback.
 *)
val mvar : LF.typ -> Id.name

val var : Comp.typ -> Id.name

val renumber : Id.name list -> Id.name -> Id.name
