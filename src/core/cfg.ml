(* .cfg file management *)

let is_cfg filename =
  Filename.check_suffix filename ".cfg"

let rec accum_lines input =
  try
    let res = input_line input in res :: accum_lines input
  with
    | End_of_file -> []

let rec trim_comment str =
  let len = String.length str in
  match str with
  | "" -> ""
  | s when s.[0] = ' '       -> trim_comment (String.sub s 1 (len - 1))
  | s when s.[0] = '\t'      -> trim_comment (String.sub s 1 (len - 1))
  | s when s.[0] = '%'       -> ""
  | s when s.[len - 1] = ' ' -> trim_comment (String.sub s 0 (len - 1))
  | s -> s

let filter_lines files =
  let files' = List.map trim_comment files in
  List.filter (fun s -> String.length s != 0) files'

(** Given a path to a cfg file and an open input channel to it,
    computes the paths to all the referenced beluga files.
 *)
let process_cfg_chan filename chan =
  let lines = accum_lines chan in
  close_in chan;
  let dir = Filename.dirname filename ^ "/" in
  List.map (fun x -> dir ^ x) (filter_lines lines)

(** Given a path to a cfg file, computes the paths to all the
    references beluga files.
 *)
let process_cfg_file filename =
  let cfg = open_in filename in
  process_cfg_chan filename cfg

let process_file_argument f =
  if is_cfg f
  then process_cfg_file f
  else [f]

