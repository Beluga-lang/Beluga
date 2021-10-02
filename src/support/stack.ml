include Stdlib.Stack

(** Pops an item from a stack and runs the given function on it.
    If the function raises an exception, the item is placed back onto
    the stack.
    The given function must not modify the stack.
  *)
let popping s f =
  let x = top_opt s in
  let y = f x in
  let _ = pop_opt s in
  y

let to_list s =
  fold (fun l x -> x :: l) [] s

let to_list_rev s =
  fold (fun k x -> fun l -> k (x :: l)) Fun.id s []
