(** Contains a family a functions for rewriting references to program
    functions.

    This is used after translation to replace all references for
    recursive calls with calls to the translated functions.
 *)

open Syntax
open Syntax.Int.Comp

type cid_map = Id.cid_prog -> Id.cid_prog

val exp_chk : cid_map -> exp_chk -> exp_chk
