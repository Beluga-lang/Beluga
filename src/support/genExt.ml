include Gen

(** Additional helpers for using generator. *)

let of_string s =
  let n = ref 0 in
  let n_max = String.length s in
  fun () ->
    if !n < n_max then (
      let c = String.get s !n in
      incr n;
      Some c)
    else None

let of_in_channel_lines chan () =
  try Some (input_line chan) with
  | _ -> None

let drop_lines g ln =
  let rec go n =
    if n <= 0 then ()
    else (
      ignore (g ());
      go (n - 1))
  in
  go ln

let line_generator ?(buffer_size = 2048) g =
  let bs = Bytes.create buffer_size in
  let finished = ref false in
  function
  | _ when !finished -> None
  | _ ->
      let got_nl = ref false in
      let i = ref 0 in
      while Bool.not !got_nl do
        let c = g () in
        match c with
        | None ->
            got_nl := true;
            finished := true
        | Some c ->
            Bytes.set bs !i c;
            incr i;
            got_nl := c = '\n'
      done;
      Some (Bytes.sub_string bs 0 !i)

let sequence gs =
  let rgs = ref gs in
  let rec go () =
    match !rgs with
    | [] -> None
    | g :: gs -> (
        match g () with
        | None ->
            rgs := gs;
            go ()
        | e -> e)
  in
  go

let iter_through f g =
  let go () =
    let open Option in
    Gen.next g $> fun x ->
    f x;
    x
  in
  go
