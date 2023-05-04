type 'a t =
  { past : 'a Stack.t
  ; future : 'a Stack.t
  }

let create () = { past = Stack.create (); future = Stack.create () }

let add { past; future } x =
  Stack.push x past;
  Stack.clear future

let step_forward { past; future } =
  match Stack.pop_opt future with
  | Option.Some x as r ->
      Stack.push x past;
      r
  | r -> r

let step_backward { past; future } =
  match Stack.pop_opt past with
  | Option.Some x as r ->
      Stack.push x future;
      r
  | r -> r

let to_lists { past; future } = Pair.both Stack.to_list_rev (past, future)
