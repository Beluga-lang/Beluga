(** Miscellaneous file handling utilities *)


(** Opens a temporary file with the given name prefix in the given
    directory and runs the given function with the path and output
    channel to that file.
    This function guarantees that even in case of exception, the
    output channel is closed and the temporary file is unlinked.
 *)
val with_temp_file : string -> string -> (string -> out_channel -> 'a) -> 'a

(** Opens an input channel on the given path and runs the given
    function with it.
    Guarantees to close the channel, even in case of exceptional exit.
 *)
val with_in_channel : string -> (in_channel -> 'a) -> 'a
