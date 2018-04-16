type 'a t =
  { force : unit -> 'a;
  }

let value (x : 'a) : 'a t = { force = fun () -> x }

let delay (f : unit -> 'a) : 'a t =
  let r = ref Maybe.Nothing in
  { force =
      fun () ->
        match !r with
        | Maybe.Just x -> x
        | Maybe.Nothing ->
           let x = f () in
           r := Maybe.Just x;
           x
  }
