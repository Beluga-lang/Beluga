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

module HelpEntry : sig
  type t =
    { option_name : OptName.t
    ; arguments : string list
    ; help_message : string option
    }
end

type help_printer = string -> Format.formatter -> unit -> unit

type +'a t

val find_opt :
     'a t
  -> string
  -> (int option * (help_printer -> string list -> unit)) option

val get_comp_value : 'a t -> string list -> ('a, Error.t) result

val get_mandatory_help_entries : 'a t -> HelpEntry.t list

val get_optional_help_entries : 'a t -> HelpEntry.t list

val opt0 : 'a -> 'a OptInfo.Unchecked.transform list -> 'a t

val opt1 :
  (string -> 'a option) -> 'a OptInfo.Unchecked.transform list -> 'a t

val bool_opt1 : bool OptInfo.Unchecked.transform list -> bool t

val int_opt1 : int OptInfo.Unchecked.transform list -> int t

val string_opt1 : string OptInfo.Unchecked.transform list -> string t

val switch_opt : bool OptInfo.Unchecked.transform list -> bool t

val takes_all_opt :
  string list OptInfo.Unchecked.transform list -> string list t

val impure_opt0 : (unit -> 'a) -> 'a OptInfo.Unchecked.transform list -> 'a t

val help_opt0 :
  (help_printer -> 'a) -> 'a OptInfo.Unchecked.transform list -> 'a t

val rest_args : (string list -> unit) -> unit t

val ( <$ ) : ('a -> 'b) -> 'a t -> 'b t

val ( <& ) : ('a -> 'b) t -> 'a t -> 'b t

val ( $> ) : 'a t -> ('a -> 'b) -> 'b t

val ( <! ) : 'a t -> unit t -> 'a t
