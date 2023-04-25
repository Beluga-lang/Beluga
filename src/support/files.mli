(** Miscellaneous file-handling utilities *)

(** [read_lines filename] is the list of ['\n'] separated lines read from the
    file at [filename]. *)
val read_lines : string -> string list

(** [with_temp_file temp_dir basename f] opens a temporary file [basename] in
    directory [temp_dir] and runs [f] with the path and output channel to
    that file. This function guarantees that even in case of exception, the
    output channel is closed and the temporary file is unlinked. *)
val with_temp_file : string -> string -> (string -> out_channel -> 'a) -> 'a

(** [with_pp_to_file filename handler] calls [handler] with a pretty-printer
    to the file at [filename]. The contents of the file are replaced by the
    outputs printed to it. *)
val with_pp_to_file : string -> (Format.formatter -> 'a) -> 'a

(** [copy_file ~source ~destination] copies the contents of file [~source] to
    the file [~destination]. *)
val copy_file : source:string -> destination:string -> unit
