(** Reader for configuration files for Beluga signatures.

    A configuration file is a list of Beluga source files, or nested
    configuration files. *)

open Beluga_syntax

(** [read_configuration ~filename] is the list of Beluga file paths to load
    as configured in [filename]. If [filename] is not a configuration file,
    then [filename] is the only Beluga file path returned.

    A configuration file is a UTF-8 encoded list of file paths. The
    configuration file may have line comments starting with [%]. Whitespaces
    in paths are supported. *)
val read_configuration : filename:string -> (Location.t * string) list
