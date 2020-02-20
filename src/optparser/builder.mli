module OptSpec : sig
  type 'a t

  val long_name : string -> 'a t
  val short_name : char -> 'a t
  val meta_vars : string list -> 'a t
  val help_msg : string -> 'a t
  val default_argument : 'a -> 'a t
  val condition : ('a -> bool) -> 'a t
  val optional : 'a -> 'a t
end

type 'a t
type opt_parser_error =
  | MissingMandatory
    of string (* option name *)
  | InvalidArgLength
    of string (* option name *)
       * int (* expected number of arguments *)
       * int (* actual number of arguments *)
  | ArgReaderFailure
    of string (* option name *)
  | NotAnOption
    of string (* option name *)

val opt0 : 'a -> 'a OptSpec.t list -> 'a t
val opt1 : (string -> 'a option) -> 'a OptSpec.t list -> 'a t

val bool_opt1 : bool OptSpec.t list -> bool t
val int_opt1 : int OptSpec.t list -> int t
val string_opt1 : string OptSpec.t list -> string t
val switch_opt : unit OptSpec.t list -> bool t

val impure_opt : (unit -> 'a) -> 'a OptSpec.t list -> 'a t
val help_opt : ((string -> Format.formatter -> unit -> unit) -> 'a) -> 'a OptSpec.t list -> 'a t
val rest_args : (string list -> unit) -> unit t

val (<$) : ('a -> 'b) -> 'a t -> 'b t
val (<&) : (('a -> 'b) t) -> 'a t -> 'b t
val ($>) : 'a t -> ('a -> 'b) -> 'b t

val (<!) : 'a t -> unit t -> 'a t

val parse : 'a t -> string list -> ('a, opt_parser_error) result
