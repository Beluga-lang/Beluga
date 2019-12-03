open Support

type t = string -> string option -> unit -> string option

let terminal : t =
  fun msg history_file () ->
  let open Maybe in
  flush_all ();
  LNoise.linenoise msg
  $> fun str ->
     match history_file with
     | None ->
        let _ = LNoise.history_add str in
        str
     | Some path ->
        let _ = LNoise.history_load ~filename:path in
        let _ = LNoise.history_add str in
        let _ = LNoise.history_save ~filename:path in
        str

let create_file (path, k) (test_start : int option) : t =
  let h = open_in path in
  let g =
    let open GenMisc in
    of_in_channel_lines h
    |> iter_through (fun x -> print_string (x ^ "\n"))
  in
  begin
    match test_start with
    | None -> ()
    | Some ln -> GenMisc.drop_lines g (ln - 1)
  end;
  match k with
  | `incomplete ->
     fun msg history_file ->
     GenMisc.sequence [g; terminal msg history_file]
  | `complete ->
     fun _ _ -> g

let create test_file test_start : t =
  match test_file with
  | None -> terminal
  | Some f -> create_file f test_start
