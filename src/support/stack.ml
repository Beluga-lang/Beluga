include Stdlib.Stack

let to_list s =
  fold (fun l x -> x :: l) [] s

let to_list_rev s =
  fold (fun k x -> fun l -> k (x :: l)) Fun.id s []
