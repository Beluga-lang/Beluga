open Support
open Beluga_syntax

module type PARSER_STATE = sig
  include State.STATE

  type token

  val peek : token option t

  val observe : token option t

  val accept : unit t

  val insert : token -> unit t
end

module type PARSER_LOCATION_STATE = sig
  include State.STATE

  type location

  val next_location : location option t

  val previous_location : location option t
end

module type BACKTRACKING_STATE = sig
  include State.STATE

  val enable_backtracking : unit t

  val disable_backtracking : unit t

  val can_backtrack : bool t

  val allow_backtracking_on_error : ('a, 'e) result t -> ('a, 'e) result t

  val with_checkpoint :
       ('a, 'e) result t
    -> ('a, [> `Backtracked of 'e | `Did_not_backtrack of 'e ]) result t
end

module type LOCATED = sig
  type t

  type location

  val location : t -> location
end

module Make_persistent_state (Token : LOCATED) : sig
  include PARSER_STATE with type token = Token.t

  include
    PARSER_LOCATION_STATE
      with type state := state
       and type location = Token.location

  include BACKTRACKING_STATE with type state := state

  val initial : ?initial_location:location -> token Seq.t -> state
end = struct
  type token = Token.t

  type location = Token.location

  (** The type of parser states. *)
  type state =
    { input : token Seq.t  (** The input stream of tokens. *)
    ; position : int
          (** The 1-based index of the state's position in the input stream.
              It is initially [0]. *)
    ; can_backtrack : bool
          (** The flag signalling whether unrestricted backtracking is
              enabled.

              This is only [true] when a parser fails with the [trying]
              combinator. *)
    ; checkpoints : state list
          (** The stack of checkpoints to backtrack to when alternating
              between parsers.

              This grows linearly with the number of nested uses of the
              [choice] combinator. *)
    ; last_location : location option
          (** The location of the last consumed token. *)
    }

  include (
    State.Make (struct
      type t = state
    end) :
      State.STATE with type state := state)

  let initial ?initial_location input =
    { input
    ; position = 0
    ; can_backtrack = false
    ; checkpoints = []
    ; last_location = initial_location
    }

  let peek =
    let* state = get in
    match state.input () with
    | Seq.Nil -> return Option.none
    | Seq.Cons (x, _xs) ->
        (* Do not advance the parser state *)
        return (Option.some x)

  let observe =
    let* state = get in
    match state.input () with
    | Seq.Nil -> return Option.none
    | Seq.Cons (x, xs) ->
        (* Advance the parser state to consume the token *)
        let* () =
          put
            { state with
              input = xs
            ; position = state.position + 1
            ; last_location = Option.some (Token.location x)
            }
        in
        return (Option.some x)

  let accept =
    (* Advance the parser state and ignore the result *)
    observe >>= fun _ -> return ()

  let enable_backtracking =
    modify (fun state -> { state with can_backtrack = true })

  let disable_backtracking =
    modify (fun state -> { state with can_backtrack = false })

  let allow_backtracking_on_error m =
    m >>= function
    | Result.Ok _ as r -> return r
    | Result.Error _ as r ->
        let* () = enable_backtracking in
        return r

  let[@inline] modify_checkpoints f =
    modify (fun state -> { state with checkpoints = f state.checkpoints })

  let[@inline] push_checkpoint checkpoint =
    modify_checkpoints (List.cons checkpoint)

  let pop_checkpoint =
    let* state = get in
    match state.checkpoints with
    | [] ->
        Error.raise_violation
          "[pop_checkpoint] no checkpoint to backtrack to"
    | checkpoint :: checkpoints ->
        let* () = put { state with checkpoints } in
        return checkpoint

  let discard_checkpoint =
    let* _checkpoint = pop_checkpoint in
    return ()

  let mark =
    let* state = get in
    push_checkpoint state

  let can_backtrack =
    let* state = get in
    return state.can_backtrack

  let can_recover to_state =
    let* from_state = get in
    return
      (from_state.can_backtrack (* Unrestricted backtracking is enabled *)
      || from_state.position = to_state.position (* No input was consumed *)
      )

  (** [backtrack checkpoint state] is [(state', ())] where [state'] is the
      result of backtracking from [state] to [checkpoint].

      Some fields from [state] may be kept in [state'], such as statistics
      for counting the number of backtrackings that occur during parsing. *)
  let backtrack checkpoint =
    let* state = get in
    put
      { state with
        input = checkpoint.input
      ; position = checkpoint.position
      ; can_backtrack = checkpoint.can_backtrack
      ; last_location = checkpoint.last_location
      }

  let with_checkpoint p =
    let* () = mark in
    p >>= function
    | Result.Ok _ as r ->
        let* () = discard_checkpoint in
        return r
    | Result.Error e -> (
        let* checkpoint = pop_checkpoint in
        can_recover checkpoint >>= function
        | true ->
            let* () = backtrack checkpoint in
            let* () = disable_backtracking in
            return (Result.error (`Backtracked e))
        | false -> return (Result.error (`Did_not_backtrack e)))

  let next_location =
    let* token_opt = peek in
    match token_opt with
    | Option.None -> return Option.none
    | Option.Some token -> return (Option.some (Token.location token))

  let previous_location =
    let* state = get in
    return state.last_location

  let insert token =
    modify (fun state -> { state with input = Seq.cons token state.input })
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

  val fail_at_next_location : exn -> 'a t

  val fail_at_previous_location : exn -> 'a t

  val labelled : string -> 'a t -> 'a t

  val span : 'a t -> (location * 'a) t

  val only : 'a t -> 'a t

  val maybe : 'a t -> 'a option t

  val void : 'a t -> unit t

  val many : 'a t -> 'a list t

  val some : 'a t -> 'a List1.t t

  val sep_by0 : sep:unit t -> 'a t -> 'a list t

  val sep_by1 : sep:unit t -> 'a t -> 'a List1.t t

  val trying : 'a t -> 'a t

  val choice : 'a t List.t -> 'a t

  val alt : 'a t -> 'a t -> 'a t

  val satisfy :
       on_token:(token -> ('a, exn) result)
    -> on_end_of_input:(unit -> 'a t)
    -> 'a t

  val eoi : unit t

  val insert_token : token -> unit t
end

module Make (State : sig
  type location = Location.t

  include PARSER_STATE

  include BACKTRACKING_STATE with type state := state

  include
    PARSER_LOCATION_STATE
      with type state := state
       and type location := location
end) :
  PARSER
    with type state = State.state
     and type token = State.token
     and type input = State.token Seq.t
     and type location = State.location = struct
  type token = State.token

  type location = State.location

  type input = State.token Seq.t

  type state = State.state

  type +'a t = State.state -> State.state * ('a, exn) result

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

  let fail_at_previous_location e =
    let open State in
    previous_location >>= function
    | Option.Some previous_location ->
        fail (located_exception1 previous_location e)
    | Option.None -> (
        next_location >>= function
        | Option.Some next_location ->
            let location =
              Location.start_position_as_location next_location
            in
            fail (located_exception1 location e)
        | Option.None -> fail e)

  let fail_at_next_location e =
    let open State in
    next_location >>= function
    | Option.Some next_location -> fail (located_exception1 next_location e)
    | Option.None -> (
        previous_location >>= function
        | Option.Some previous_location ->
            let location =
              Location.stop_position_as_location previous_location
            in
            fail (located_exception1 location e)
        | Option.None -> fail e)

  let return_at s x = (s, Result.ok x)

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

  let trying p =
    let open State in
    allow_backtracking_on_error p

  let label p label =
    catch p (function
      | s, Result.Error (Labelled_exception { cause; _ }) ->
          (s, Result.error (Labelled_exception { cause; label }))
      | s, Result.Error cause ->
          (s, Result.error (Labelled_exception { cause; label }))
      | x -> x)

  let labelled l p = label p l

  let choice =
    let open State in
    let rec choice_aux ps errors =
      match ps with
      | [] -> fail_at_next_location (No_more_choices errors)
      | p :: ps' -> (
          with_checkpoint p >>= function
          | Result.Ok _ as r -> return r
          | Result.Error (`Backtracked e) -> choice_aux ps' (e :: errors)
          | Result.Error (`Did_not_backtrack e) -> return (Result.error e))
    in
    fun ps -> choice_aux ps []

  let[@inline] alt p1 p2 = choice [ p1; p2 ]

  let maybe p = alt (p $> Option.some) (return Option.none)

  let void p = p $> fun _x -> ()

  let rec many p = alt (some p $> List1.to_list) (return [])

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

  let next_location =
    let open State in
    next_location $> Result.ok

  let previous_location =
    let open State in
    previous_location $> Result.ok

  let span p =
    let* l1_opt = next_location
    and* x = p
    and* l2_opt = previous_location in
    match (l1_opt, l2_opt) with
    | Option.None, Option.None ->
        (* There are no tokens in the input stream *)
        return (Location.ghost, x)
    | Option.Some l1, Option.None -> return (l1, x)
    | Option.None, Option.Some l2 -> return (l2, x)
    | Option.Some l1, Option.Some l2 ->
        let filename = Location.filename l1
        and start_position = Location.start_position l1
        and stop_position = Location.stop_position l2 in
        let l =
          if Position.(start_position < stop_position) then
            (* The parser [p] consumed some tokens *)
            Location.make ~filename ~start_position ~stop_position
          else
            (* The parser [p] did not consume any tokens, so this location
               does not include any token *)
            Location.make ~filename ~start_position:stop_position
              ~stop_position:start_position
        in
        return (l, x)

  let eoi =
    let open State in
    peek
    >>= (function
          | Option.None -> return (Result.ok ())
          | Option.Some _token -> fail_at_next_location Expected_end_of_input)
    |> labelled "end of input"

  let only p = p <& eoi

  let satisfy ~on_token ~on_end_of_input =
    let open State in
    peek >>= function
    | Option.None -> on_end_of_input ()
    | Option.Some token -> (
        match on_token token with
        | Result.Ok _ as r ->
            let* () = accept in
            return r
        | Result.Error cause -> fail_at_next_location cause)

  let insert_token token =
    let open State in
    let* () = insert token in
    return (Result.ok ())
end
