type 'a t =
  { past : 'a Stack.t
  ; future : 'a Stack.t
  }

let create () =
  { past = Stack.create ()
  ; future = Stack.create ()
  }

let add { past; future } x =
  Stack.push x past;
  Stack.clear future

module Direction = struct
  type t = [ `forward | `backward ]

  let inverse = function
    | `forward -> `backward
    | `backward -> `forward
end

let step d { past; future } =
  let open Maybe in
  match d with
  | `forward ->
     Misc.Stack.pop_opt future
     $> fun x -> Stack.push x past; x
  | `backward ->
     Misc.Stack.pop_opt past
     $> fun x -> Stack.push x future; x

let to_lists { past; future } =
  Pair.both Misc.Stack.to_list_rev (past, future)
