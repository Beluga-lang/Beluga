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
  let g = GenMisc.of_in_channel_lines h in
  let g_mirror =
    GenMisc.iter_through (fun x -> print_string (x ^ "\n")) g
  in
  let g_mirror_with msg =
    let open GenMisc in
    iter_through (fun x -> print_string msg; print_string (x ^ "\n")) g
  in
  begin
    match test_start with
    | None -> ()
    | Some ln -> GenMisc.drop_lines g_mirror (ln - 1)
  end;
  match k with
  | `incomplete ->
     fun msg history_file ->
     GenMisc.sequence [g_mirror_with msg; terminal msg history_file]
  | `complete ->
     fun msg _ _ ->
     print_string msg;
     g_mirror ()

let create test_file test_start : t =
  match test_file with
  | None -> terminal
  | Some f -> create_file f test_start
