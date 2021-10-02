(**
   An internal module for utility functions used in this package.
   @author Clare Jang
 *)

let id a = a

module List = struct
  include Stdlib.List

  let take_circularly n ls =
    let rec go n =
      function
      | _ when n <= 0 -> []
      | [] ->
         go n ls
      | x :: xs ->
         x :: go (n - 1) xs
    in
    if ls = []
    then raise (Invalid_argument "'ls' should have more than one element")
    else go n ls
end
