let go finalize body =
  try
    let x = body () in
    finalize ();
    x
  with
  | e ->
     finalize ();
     raise e

let with_temp_file temp_dir template f =
  let (path, out) = Filename.open_temp_file ~temp_dir: temp_dir template "" in
  let finalize () =
    List.iter (fun f -> Misc.noexcept f)
      [ (fun _ -> close_out out)
      ; (fun _ -> Sys.remove path)
      ]
  in
  go finalize (fun _ -> f path out)

let with_in_channel path f =
  let input = open_in path in
  let finalize () = Misc.noexcept (fun _ -> close_in input) in
  go finalize (fun _ -> f input)
