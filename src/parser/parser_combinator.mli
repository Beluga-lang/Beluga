open Support
open Beluga_syntax

module type PARSER_STATE = sig
  include State.STATE

  type token

  val peek : token option t

  val observe : token option t

  val accept : unit t
end

module type PARSER_LOCATION_STATE = sig
  include State.STATE

  type location

  val next_location : location option t

  val previous_location : location option t
end

module type TOGGLEABLE_BACKTRACKING_STATE = sig
  include State.STATE

  val with_unlimited_backtracking : ('a, 'e) result t -> ('a, 'e) result t
end

module type BACKTRACKING_STATE = sig
  include State.STATE

  exception No_checkpoints

  val with_checkpoint :
       ('a, 'e) result t
    -> ('a, [> `Backtracked of 'e | `Did_not_backtrack of 'e ]) result t
end

module type LOCATED = sig
  type t

  type location

  val location : t -> location
end

module Make_state (Token : LOCATED) : sig
  include PARSER_STATE with type token = Token.t

  include
    PARSER_LOCATION_STATE
      with type state := state
       and type location = Token.location

  include BACKTRACKING_STATE with type state := state

  include TOGGLEABLE_BACKTRACKING_STATE with type state := state

  val initial : ?initial_location:location -> token Seq.t -> state
end

module type PARSER = sig
  type token

  type location

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

  val run : 'a t -> state -> state * ('a, exn) result

  val run_exn : 'a t -> state -> state * 'a

  val catch :
    'a t -> (state * ('a, exn) result -> state * ('b, exn) result) -> 'b t

  val fail : exn -> 'a t

  val span : 'a t -> (location * 'a) t

  val fail_at_next_location : exn -> 'a t

  val fail_at_previous_location : exn -> 'a t

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

module Make (State : sig
  type location = Location.t

  include PARSER_STATE

  include BACKTRACKING_STATE with type state := state

  include TOGGLEABLE_BACKTRACKING_STATE with type state := state

  include
    PARSER_LOCATION_STATE
      with type state := state
       and type location := location
end) :
  PARSER
    with type state = State.state
     and type token = State.token
     and type input = State.token Seq.t
     and type location = State.location
