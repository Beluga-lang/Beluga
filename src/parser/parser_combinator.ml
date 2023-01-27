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

module Make_persistent_bracktracking_state (Token : sig
  type t
end) : sig
  include PARSER_STATE with type token = Token.t

  include PARSER_BACKTRACKING_STATE with type t := t

  val initial : token Seq.t -> t
end = struct
  type token = Token.t

  type t =
    { input : token Seq.t
    ; position : int
    ; can_backtrack : bool
    }

  let initial input = { input; position = 0; can_backtrack = false }

  let[@inline] position s = s.position

  let[@inline] enable_backtracking s = { s with can_backtrack = true }

  let[@inline] disable_backtracking s = { s with can_backtrack = false }

  let[@inline] is_backtracking_enabled s = s.can_backtrack

  let observe s =
    match s.input () with
    | Seq.Nil -> Option.none
    | Seq.Cons (x, xs) ->
        let s' = { s with input = xs; position = s.position + 1 } in
        Option.some (x, s')

  let[@inline] has_not_consumed_input ~from ~to_ =
    position from = position to_

  let can_backtrack ~from ~to_ =
    if is_backtracking_enabled from then true
    else has_not_consumed_input ~from ~to_
end

module Make_location_state (Token : sig
  type t

  val location : t -> Location.t
end) (State : sig
  include PARSER_STATE with type token = Token.t

  include PARSER_BACKTRACKING_STATE with type t := t
end) : sig
  include module type of State

  include
    PARSER_LOCATION_STATE with type t := t and type location = Location.t

  val initial : ?last_location:Location.t -> State.t -> t
end = struct
  type location = Location.t

  type token = Token.t

  type t =
    { inner_state : State.t
    ; last_location : Location.t option
    }

  let initial ?last_location inner_state = { inner_state; last_location }

  let[@inline] modify_inner_state f state =
    { state with inner_state = f state.inner_state }

  let enable_backtracking = modify_inner_state State.enable_backtracking

  let disable_backtracking = modify_inner_state State.disable_backtracking

  let is_backtracking_enabled s = State.is_backtracking_enabled s.inner_state

  let[@inline] observe s =
    let open Option in
    State.observe s.inner_state $> fun (t, inner_state') ->
    let location = Token.location t in
    let s' =
      { inner_state = inner_state'; last_location = Option.some location }
    in
    (t, s')

  let can_backtrack ~from ~to_ =
    State.can_backtrack ~from:from.inner_state ~to_:to_.inner_state

  let next_location s =
    let open Option in
    observe s $> fun (token, _s') -> Token.location token

  let previous_location s = s.last_location
end

module Make_parser_with_locations (Token : sig
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
     and type location = Location.t = struct
  type token = Token.t

  type location = Location.t

  type input = Token.t Seq.t

  type state = State.t

  type +'a t = State.t -> State.t * ('a, exn) result

  type 'a parser = 'a t

  exception Parser_error of exn

  exception
    Labelled_exception of
      { label : string
      ; cause : exn
      }

  exception No_more_choices of exn list

  exception Expected_end_of_input

  (** [Parser_located_exception { cause; locations }] is the exception
      [cause] annotated with source file [locations].

      This exception is analogous to the [Located_exception] variant from the
      {!Error} module, but we need to rearrange the exceptions with
      {!restructure_parser_exception} since we're manually handling errors in
      the parser combinators. *)
  exception
    Parser_located_exception of
      { cause : exn
      ; locations : location List1.t
      }

  (** [flatten_exhausted_choices_exception_aux exceptions_rev acc] simplifies
      the structure of the list of exceptions [exceptions_rev] retrieved from
      a {!No_more_choices} exception by discarding their locations and
      transforming the tree of exceptions to a list. *)
  let rec flatten_exhausted_choices_exception_aux exceptions_rev acc =
    match exceptions_rev with
    | [] -> acc
    | e :: es -> (
        match discard_exception_locations e with
        | Labelled_exception { label; cause } ->
            let cause' = discard_exception_locations cause in
            flatten_exhausted_choices_exception_aux es
              (Labelled_exception { label; cause = cause' } :: acc)
        | No_more_choices e ->
            flatten_exhausted_choices_exception_aux es
              (flatten_exhausted_choices_exception_aux e acc)
        | e -> flatten_exhausted_choices_exception_aux es (e :: acc))

  and flatten_exhausted_choices_exception = function
    | No_more_choices causes_rev ->
        let causes' =
          flatten_exhausted_choices_exception_aux causes_rev []
        in
        No_more_choices causes'
    | Parser_located_exception { cause; locations } ->
        let cause' = flatten_exhausted_choices_exception cause in
        Parser_located_exception { cause = cause'; locations }
    | Labelled_exception { label; cause } ->
        let cause' = flatten_exhausted_choices_exception cause in
        Labelled_exception { label; cause = cause' }
    | Parser_error cause ->
        let cause' = flatten_exhausted_choices_exception cause in
        Parser_error cause'
    | exn -> exn

  (** [discard_exception_locations exn] traverses the parser exception [exn]
      and removes those constructed with {!Parser_located_exception}. *)
  and discard_exception_locations = function
    | Parser_located_exception { cause; _ } ->
        discard_exception_locations cause
    | Labelled_exception { label; cause } ->
        let cause' = discard_exception_locations cause in
        Labelled_exception { label; cause = cause' }
    | No_more_choices causes ->
        let causes' = List.map discard_exception_locations causes in
        No_more_choices causes'
    | Parser_error cause ->
        let cause' = discard_exception_locations cause in
        Parser_error cause'
    | exn -> exn

  (** [bubble_up_exception_locations exn] transforms the parser exception
      [exn] structure by bringing sub-exceptions constructed with
      {!Parser_located_exception} to the top of the tree or choice branch.
      This ensures that no {!Parser_located_exception} is wrapped in a
      {!Labelled_exception}, which would happen since labels are added as we
      exit the parser call stack. *)
  and bubble_up_exception_locations = function
    | Parser_located_exception { cause; locations } ->
        let cause' = bubble_up_exception_locations cause in
        Parser_located_exception { cause = cause'; locations }
    | Labelled_exception
        { label; cause = Parser_located_exception { cause; locations } } ->
        let cause' = bubble_up_exception_locations cause in
        Parser_located_exception
          { cause =
              bubble_up_exception_locations
                (Labelled_exception { label; cause = cause' })
          ; locations
          }
    | Parser_error (Parser_located_exception { cause; locations }) ->
        let cause' = bubble_up_exception_locations cause in
        Parser_located_exception
          { cause = bubble_up_exception_locations (Parser_error cause')
          ; locations
          }
    | No_more_choices causes ->
        let causes' = List.map bubble_up_exception_locations causes in
        No_more_choices causes'
    | exn -> exn

  (** [annotate_parser_error exn] adds an annotation on the topmost exception
      produced by the parser to specify that the exception is a parser
      exception. *)
  and annotate_parser_error = function
    | Parser_located_exception { cause; locations } ->
        let cause' = annotate_parser_error cause in
        Parser_located_exception { cause = cause'; locations }
    | exn -> Parser_error exn

  (** [convert_located_exceptions exn] converts {!Parser_located_exception}
      in [exn] to located exceptions in the {!Error} module for
      error-reporting. *)
  and convert_located_exceptions = function
    | Parser_located_exception { cause; locations } ->
        let cause' = convert_located_exceptions cause in
        Error.located_exception locations cause'
    | Labelled_exception { label; cause } ->
        let cause' = convert_located_exceptions cause in
        Labelled_exception { label; cause = cause' }
    | No_more_choices causes ->
        let causes' = List.map convert_located_exceptions causes in
        No_more_choices causes'
    | Parser_error cause ->
        let cause' = convert_located_exceptions cause in
        Parser_error cause'
    | exn -> exn

  (** [restructure_parser_exception exn] restructures the parser exception
      [exn] to simplify it for error-reporting. *)
  let restructure_parser_exception =
    Fun.(
      bubble_up_exception_locations >> flatten_exhausted_choices_exception
      >> annotate_parser_error >> convert_located_exceptions)

  let[@inline] run p s = p s

  let[@inline] run_exn p s =
    match run p s with
    | s', Result.Ok e -> (s', e)
    | _s', Result.Error cause ->
        let cause' = restructure_parser_exception cause in
        Error.raise cause'

  let catch p handler s = run p s |> handler

  let fail e s = (s, Result.error e)

  let located_exception locations cause =
    Parser_located_exception { locations; cause }

  let located_exception1 location cause =
    located_exception (List1.singleton location) cause

  let fail_at_previous_location e s =
    match State.previous_location s with
    | Option.Some previous_location ->
        fail (located_exception1 previous_location e) s
    | Option.None -> (
        match State.next_location s with
        | Option.Some next_location ->
            fail
              (located_exception1
                 (Location.start_position_as_location next_location)
                 e)
              s
        | Option.None -> fail e s)

  let fail_at_next_location e s =
    match State.next_location s with
    | Option.Some next_location ->
        fail (located_exception1 next_location e) s
    | Option.None -> (
        match State.previous_location s with
        | Option.Some previous_location ->
            fail
              (located_exception1
                 (Location.stop_position_as_location previous_location)
                 e)
              s
        | Option.None -> fail e s)

  let return_at s x = (s, Result.ok x)

  let get_state s = return_at s s

  let put_state s _s = return_at s ()

  module M = Monad.Make (struct
    type nonrec 'a t = 'a t

    let return x s = return_at s x

    let bind k p s =
      match run p s with
      | s', Result.Ok x -> run (k x) s'
      | s', (Result.Error _ as e) -> (s', e)
  end)

  include (M : Monad.MONAD with type 'a t := 'a t)

  include (Functor.Make (M) : Functor.FUNCTOR with type 'a t := 'a t)

  include (Apply.Make (M) : Apply.APPLY with type 'a t := 'a t)

  let trying p s =
    match run p s with
    | s, (Result.Error _ as e) ->
        let s' = State.enable_backtracking s in
        (s', e)
    | x -> x

  let label p label =
    catch p (function
      | s, Result.Error (Labelled_exception { cause; _ }) ->
          (s, Result.error (Labelled_exception { cause; label }))
      | s, Result.Error cause ->
          (s, Result.error (Labelled_exception { cause; label }))
      | x -> x)

  let labelled l p = label p l

  let choice ps s =
    let rec go es = function
      | [] -> fail_at_next_location (No_more_choices es)
      | p :: ps' ->
          catch p (function
            | s', Result.Error e when State.can_backtrack ~from:s' ~to_:s ->
                run (go (e :: es) ps') s
            | x -> x)
    in
    run (go [] ps) s

  let[@inline] alt p1 p2 = choice [ p1; p2 ]

  let[@inline] ( <|> ) p1 p2 = alt p1 p2

  let maybe p = p $> Option.some <|> return Option.none

  let void p = p $> fun _x -> ()

  let rec many p = some p $> List1.to_list <|> return []

  and some p =
    let* x = p in
    let* xs = many p in
    return (List1.from x xs)

  let sep_by0 ~sep p =
    maybe p >>= function
    | Option.None -> return []
    | Option.Some x ->
        let* xs = many (sep &> p) in
        return (x :: xs)

  let sep_by1 ~sep p =
    let* x = p in
    let* xs = many (sep &> p) in
    return (List1.from x xs)

  let next_location = get_state $> State.next_location

  let previous_location = get_state $> State.previous_location

  let span p =
    let* l1_opt = next_location
    and* x = p
    and* l2_opt = previous_location in
    match (l1_opt, l2_opt) with
    | Option.None, Option.Some l2 -> return (l2, x)
    | Option.Some l1, Option.Some l2 ->
        let l = Location.between ~start:l1 ~stop:l2 in
        return (l, x)
    | _, Option.None ->
        assert
          false (* The parser [p] succeeded, so [l2_opt <> Option.none]. *)

  let eoi s =
    match State.observe s with
    | Option.None -> return_at s ()
    | Option.Some (_token, s') ->
        fail_at_previous_location Expected_end_of_input s'

  let only p = p <& eoi

  let satisfy ~on_token ~on_end_of_input s =
    match State.observe s with
    | Option.None -> on_end_of_input () s
    | Option.Some (token, s') -> (
        match on_token token with
        | Result.Ok r -> return_at s' r
        | Result.Error cause -> fail_at_next_location cause s)
end

module Make (Token : sig
  type t

  val location : t -> Location.t
end) : sig
  include
    PARSER_WITH_LOCATIONS
      with type token = Token.t
       and type input = Token.t Seq.t
       and type location = Location.t

  val initial_state : ?last_location:location -> input -> state
end = struct
  module Simple_state = Make_persistent_bracktracking_state (Token)
  module State_with_locations = Make_location_state (Token) (Simple_state)
  include Make_parser_with_locations (Token) (State_with_locations)

  let initial_state ?last_location input =
    State_with_locations.initial ?last_location (Simple_state.initial input)
end
