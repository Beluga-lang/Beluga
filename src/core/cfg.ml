(* .cfg file management *)

let is_cfg file_name =
  Filename.check_suffix file_name ".cfg"

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

let process_cfg_file file_name =
  let cfg = open_in file_name in
  let lines = accum_lines cfg in
  close_in cfg
  ; let dir = Filename.dirname file_name ^ "/" in
    List.map (fun x -> dir ^ x) (filter_lines lines)

let process_file_argument f =
  if is_cfg f
  then process_cfg_file f
  else [f]

