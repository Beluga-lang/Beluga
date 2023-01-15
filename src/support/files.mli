(** Miscellaneous file-handling utilities *)

(** [read_lines filename] is the list of ['\n'] separated lines read from the
    file at [filename]. *)
val read_lines : string -> string list

(** [with_temp_file temp_dir basename f] opens a temporary file [basename] in
    directory [temp_dir] and runs [f] with the path and output channel to
    that file. This function guarantees that even in case of exception, the
    output channel is closed and the temporary file is unlinked. *)
val with_temp_file : string -> string -> (string -> out_channel -> 'a) -> 'a

(** [with_in_channel filename f] opens an input channel on [filename] and
    runs [f] with it. Guarantees to close the channel, even in case of
    exceptional exit. *)
val with_in_channel : string -> (in_channel -> 'a) -> 'a

(** [with_open_bin filename f] opens an input channel on [filename] in binary
    mode and runs [f] with it. The channel is guaranteed to be closed after
    calling [f], even in case of exceptional exit. *)
val with_open_bin : string -> (in_channel -> 'a) -> 'a

(** [with_pp_to_file filename handler] calls [handler] with a pretty-printer
    to the file at [filename]. The contents of the file are replaced by the
    outputs printed it. *)
val with_pp_to_file : string -> (Format.formatter -> unit) -> unit
