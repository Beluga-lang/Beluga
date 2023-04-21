let read_lines file =
  let contents = In_channel.with_open_bin file In_channel.input_all in
  String.split_on_char '\n' contents

let go finalize body =
  try
    let x = body () in
    finalize ();
    x
  with
  | e ->
      finalize ();
      raise e

let with_temp_file temp_dir basename f =
  let path, out = Filename.open_temp_file ~temp_dir basename "" in
  let finalize () =
    List.iter
      (fun f -> Misc.noexcept f)
      [ (fun () -> close_out out); (fun () -> Sys.remove path) ]
  in
  go finalize (fun () -> f path out)

let with_in_channel path f =
  let input = open_in path in
  let finalize () = Misc.noexcept (fun () -> close_in input) in
  go finalize (fun () -> f input)

let with_pp_to_file filename f =
  let out_channel = Out_channel.open_bin filename in
  try
    let ppf = Format.formatter_of_out_channel out_channel in
    let x = f ppf in
    Out_channel.close out_channel;
    x
  with
  | cause ->
      Out_channel.close_noerr out_channel;
      raise cause

let copy_file ~source ~destination =
  let buffer_size = 4096 in
  let buffer = Bytes.create buffer_size in
  let input_channel = In_channel.open_bin source in
  let output_channel = Out_channel.open_bin destination in
  try
    let bytes_read_count = ref 0 in
    while
      bytes_read_count := In_channel.input input_channel buffer 0 buffer_size;
      !bytes_read_count <> 0
    do
      Out_channel.output output_channel buffer 0 !bytes_read_count
    done;
    In_channel.close input_channel;
    Out_channel.close output_channel
  with
  | cause ->
      In_channel.close_noerr input_channel;
      Out_channel.close_noerr output_channel;
      raise cause
