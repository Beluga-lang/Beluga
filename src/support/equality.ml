(** A restricted form of the equality operator that works only for
    integers.

    Fully polymorphic equality is dangerous and limits refactorability
    of the code, so every module should open this one to avoid using
    polymorphic equality.
 *)
let (=) (x : int) (y : int) = (x = y)
