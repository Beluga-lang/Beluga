open Support

type t = msg:string -> history_file:string option -> string Gen.gen

let terminal : t =
 fun ~msg ~history_file () ->
  let open Option in
  Out_channel.flush_all ();
  LNoise.linenoise msg $> fun str ->
  match history_file with
  | Option.None ->
      let _ = LNoise.history_add str in
      str
  | Option.Some path ->
      let _ = LNoise.history_load ~filename:path in
      let _ = LNoise.history_add str in
      let _ = LNoise.history_save ~filename:path in
      str

let create_file { Options.filename = path; kind = k }
    (test_start : int option) : t =
  let h (* This input channel is never closed *) =
    In_channel.open_bin path
  in
  let g = Gen.of_in_channel_lines h in
  let g_mirror =
    Gen.iter_through
      (fun x -> Format.fprintf Format.std_formatter "%s@\n" x)
      g
  in
  let g_mirror_with msg =
    Gen.iter_through
      (fun x -> Format.fprintf Format.std_formatter "%s%s@\n" msg x)
      g
  in
  (match test_start with
  | Option.None -> ()
  | Option.Some ln -> Gen.drop_lines g_mirror (ln - 1));
  match k with
  | `incomplete ->
      fun ~msg ~history_file ->
        Gen.sequence [ g_mirror_with msg; terminal ~msg ~history_file ]
  | `complete ->
      fun ~msg ~history_file:_ _ ->
        Format.pp_print_string Format.std_formatter msg;
        g_mirror ()

let make test_file test_start : t =
  match test_file with
  | Option.None -> terminal
  | Option.Some f -> create_file f test_start

let next_line_opt prompt ~msg ~history_file = prompt ~msg ~history_file ()
