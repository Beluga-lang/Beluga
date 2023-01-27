open Support
open Beluga_syntax

module type PARSER_STATE = sig
  type t

  type token

  val observe : t -> (token * t) option
end

module type PARSER_BACKTRACKING_STATE = sig
  type t

  val enable_backtracking : t -> t

  val disable_backtracking : t -> t

  val is_backtracking_enabled : t -> bool

  val can_backtrack : from:t -> to_:t -> bool
end

module type PARSER_LOCATION_STATE = sig
  type t

  type location

  val next_location : t -> location option

  val previous_location : t -> location option
end

module type LOCATED_TOKEN = sig
  type t

  val location : t -> Location.t
end

module Make_persistent_parser_state (Token : LOCATED_TOKEN) : sig
  include PARSER_STATE with type token = Token.t

  include PARSER_BACKTRACKING_STATE with type t := t

  include
    PARSER_LOCATION_STATE with type t := t and type location = Location.t

  val initial_state : ?last_location:Location.t -> Token.t Seq.t -> t
end

module type PARSER = sig
  type token

  type input

  type state

  type 'a t = state -> state * ('a, exn) result

  type 'a parser = 'a t

  exception Parser_error of exn

  exception
    Labelled_exception of
      { label : string
      ; cause : exn
      }

  exception No_more_choices of exn list

  exception Expected_end_of_input

  include Monad.MONAD with type 'a t := 'a t

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t

  val get_state : state t

  val put_state : state -> unit t

  val run : 'a t -> state -> state * ('a, exn) result

  val run_exn : 'a t -> state -> state * 'a

  val catch :
    'a t -> (state * ('a, exn) result -> state * ('b, exn) result) -> 'b t

  val fail : exn -> 'a t

  val labelled : string -> 'a t -> 'a t

  val only : 'a t -> 'a t

  val maybe : 'a t -> 'a option t

  val void : 'a t -> unit t

  val many : 'a t -> 'a list t

  val some : 'a t -> 'a List1.t t

  val sep_by0 : sep:unit t -> 'a t -> 'a list t

  val sep_by1 : sep:unit t -> 'a t -> 'a List1.t t

  val trying : 'a t -> 'a t

  val alt : 'a t -> 'a t -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t

  val choice : 'a t List.t -> 'a t

  val satisfy :
       on_token:(token -> ('a, exn) result)
    -> on_end_of_input:(unit -> 'a t)
    -> 'a t

  val eoi : unit t
end

module type PARSER_WITH_LOCATIONS = sig
  include PARSER

  type location

  exception
    Parser_located_exception of
      { cause : exn
      ; locations : location List1.t
      }

  val span : 'a t -> (location * 'a) t

  val fail_at_next_location : exn -> 'a t

  val fail_at_previous_location : exn -> 'a t
end

module Make (Token : sig
  type t
end) (State : sig
  include PARSER_STATE with type token = Token.t

  include PARSER_BACKTRACKING_STATE with type t := t

  include
    PARSER_LOCATION_STATE with type t := t and type location = Location.t
end) :
  PARSER_WITH_LOCATIONS
    with type state = State.t
     and type token = Token.t
     and type input = Token.t Seq.t
     and type location = Location.t
