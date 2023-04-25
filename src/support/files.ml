let read_lines file =
  let contents = In_channel.with_open_bin file In_channel.input_all in
  String.split_on_char '\n' contents

let with_temp_file temp_dir basename f =
  let path, out = Filename.open_temp_file ~temp_dir basename "" in
  Fun.protect
    ~finally:(fun () ->
      Out_channel.close_noerr out;
      Misc.noexcept (fun () -> Sys.remove path))
    (fun () -> f path out)

let with_pp_to_file filename f =
  Out_channel.with_open_bin filename (fun out_channel ->
      let ppf = Format.formatter_of_out_channel out_channel in
      f ppf)

let copy_file ~source ~destination =
  let buffer_size = 4096 in
  let buffer = Bytes.create buffer_size in
  In_channel.with_open_bin source (fun input_channel ->
      Out_channel.with_open_bin destination (fun output_channel ->
          let bytes_read_count = ref 0 in
          while
            bytes_read_count :=
              In_channel.input input_channel buffer 0 buffer_size;
            !bytes_read_count <> 0
          do
            Out_channel.output output_channel buffer 0 !bytes_read_count
          done))
