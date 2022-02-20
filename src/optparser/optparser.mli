type +'a option_specification

type 'a option_specification_step

type 'a option_specification_steps = 'a option_specification_step list

val long_name : string -> 'a option_specification_step

val short_name : char -> 'a option_specification_step

val other_names : string list -> 'a option_specification_step

val help_message : string -> 'a option_specification_step

val default_argument : 'a -> 'a option_specification_step

val meta_variables : string list -> 'a option_specification_step

val optional : 'a -> 'a option_specification_step

type help_printer = string -> Format.formatter -> unit -> unit

type +'a options_specification

val opt0 : 'a -> 'a option_specification_steps -> 'a options_specification

val opt1 :
     (string -> 'a option)
  -> 'a option_specification_steps
  -> 'a options_specification

val bool_opt1 : bool option_specification_steps -> bool options_specification

val int_opt1 : int option_specification_steps -> int options_specification

val string_opt1 :
  string option_specification_steps -> string options_specification

val switch_opt :
  bool option_specification_steps -> bool options_specification

val impure_opt0 :
  (unit -> 'a) -> 'a option_specification_steps -> 'a options_specification

val help_opt0 :
     (help_printer -> 'a)
  -> 'a option_specification_steps
  -> 'a options_specification

val rest_args : (string list -> unit) -> unit options_specification

val ( <$ ) :
  ('a -> 'b) -> 'a options_specification -> 'b options_specification

val ( <& ) :
     ('a -> 'b) options_specification
  -> 'a options_specification
  -> 'b options_specification

val ( $> ) :
  'a options_specification -> ('a -> 'b) -> 'b options_specification

val ( <! ) :
     'a options_specification
  -> unit options_specification
  -> 'a options_specification

module Error : sig
  module Option : sig
    type option_error = { option_name : string }
  end

  module Argument : sig
    type invalid_arguments_length_error =
      { option_name : string
      ; expected_argument_count : int
      ; actual_argument_count : int
      }
  end

  type t =
    [ `Missing_mandatory_option of Option.option_error
    | `Invalid_arguments_length of Argument.invalid_arguments_length_error
    | `Argument_reader_failure of Option.option_error
    | `Not_an_option of Option.option_error
    ]
end

val parse : 'a options_specification -> string list -> ('a, Error.t) result
