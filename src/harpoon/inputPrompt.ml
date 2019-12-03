open Support

type get_input = string -> string option -> unit -> string option
type set_hints = (string -> (string * bool) option) -> unit
type t =
  { get_input : get_input
  ; set_hints : set_hints
  }

let terminal : get_input =
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

let create_file (path, k) (test_start : int option) : get_input =
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

let create_hints_callback cb : string -> (string * LNoise.hint_color * bool) option =
  fun str ->
  let open Maybe in
  cb str
  $> (fun (hint, bold) -> (hint, LNoise.Yellow, bold))

let create test_file test_start : t =
  { get_input =
      begin match test_file with
      | None -> terminal
      | Some f -> create_file f test_start
      end
  ; set_hints =
      fun cb ->
      LNoise.set_hints_callback (create_hints_callback cb)
  }
