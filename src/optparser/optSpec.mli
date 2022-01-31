type error =
  | MissingMandatory of string (* option name *)
  | InvalidArgLength of
      string (* option name *) * int (* expected number of arguments *) * int
  (* actual number of arguments *)
  | ArgReaderFailure of string (* option name *)
  | NotAnOption of string
(* option name *)

type help_entry =
  OptName.t (* option name *)
  * string list
  (* names for arguments *)
  * string option
(* help message for option *)

type help_printer = string -> Format.formatter -> unit -> unit

type 'a t

val find_opt :
     'a t
  -> string
  -> (int option * (help_printer -> string list -> unit)) option

val get_comp_value : 'a t -> string list -> ('a, error) result

val get_mandatory_help_entries : 'a t -> help_entry list

val get_optional_help_entries : 'a t -> help_entry list

val opt0 : 'a -> 'a OptInfo.Unchecked.t list -> 'a t

val opt1 : (string -> 'a option) -> 'a OptInfo.Unchecked.t list -> 'a t

val bool_opt1 : bool OptInfo.Unchecked.t list -> bool t

val int_opt1 : int OptInfo.Unchecked.t list -> int t

val string_opt1 : string OptInfo.Unchecked.t list -> string t

val switch_opt : unit OptInfo.Unchecked.t list -> bool t

val takes_all_opt : string list OptInfo.Unchecked.t list -> string list t

val impure_opt0 : (unit -> 'a) -> 'a OptInfo.Unchecked.t list -> 'a t

val help_opt0 : (help_printer -> 'a) -> 'a OptInfo.Unchecked.t list -> 'a t

val rest_args : (string list -> unit) -> unit t

val ( <$ ) : ('a -> 'b) -> 'a t -> 'b t

val ( <& ) : ('a -> 'b) t -> 'a t -> 'b t

val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

val ( <! ) : 'a t -> unit t -> 'a t
