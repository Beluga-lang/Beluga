type 'a t =
  { force : unit -> 'a;
  }

let value (x : 'a) : 'a t = { force = fun () -> x }

let delay (f : unit -> 'a) : 'a t =
  let r = ref None in
  { force =
      fun () ->
      !r |>
        Maybe.eliminate
          (fun () ->
            let x = f () in
            r := Some x;
            x)
          (fun x -> x)
  }
