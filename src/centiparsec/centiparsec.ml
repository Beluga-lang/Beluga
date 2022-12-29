open Support

module type PARSER = sig
  type token

  type input

  type state

  type 'a t = state -> state * ('a, exn) result

  type 'a parser = 'a t

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

  val only : 'a t -> 'a t

  val maybe : 'a t -> 'a option t

  val maybe_default : 'a t -> default:'a -> 'a t

  val void : 'a t -> unit t

  val sequence : 'a t list -> 'a list t

  val many : 'a t -> 'a list t

  val some : 'a t -> 'a List1.t t

  val sep_by0 : 'a t -> unit t -> 'a list t

  val sep_by1 : 'a t -> unit t -> 'a List1.t t

  val traverse : ('a -> 'b t) -> 'a list -> 'b list t

  val traverse_void : ('a -> unit t) -> 'a list -> unit t

  val trying : 'a t -> 'a t

  val alt : 'a t -> 'a t -> 'a t

  val choice : 'a t List.t -> 'a t

  val satisfy : (token -> ('a, exn) result) -> 'a t

  val eoi : unit t

  val labelled : string -> 'a t -> 'a t

  val renamed : string -> 'a t -> 'a t
end

module type SIMPLE_STATE = sig
  type token

  type t

  val enable_backtracking : t -> t

  val disable_backtracking : t -> t

  val observe : t -> (token * t) option

  val can_backtrack : from:t -> to_:t -> bool
end

module Make_simple_state (Token : sig
  type t
end) : sig
  include SIMPLE_STATE with type token = Token.t

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

  let observe s =
    match s.input () with
    | Seq.Nil -> Option.none
    | Seq.Cons (x, xs) ->
        let s' = { s with input = xs; position = s.position + 1 } in
        Option.some (x, s')

  let[@inline] has_consumed_input ~from ~to_ = position from = position to_

  let can_backtrack ~from ~to_ =
    if from.can_backtrack then true else has_consumed_input ~from ~to_
end

module type STATE_WITH_LOCATION = sig
  include SIMPLE_STATE

  type location

  val next_location : t -> location option

  val previous_location : t -> location option
end

module Make_location_state (Location : sig
  type t
end) (Token : sig
  type t

  val location : t -> Location.t
end)
(State : SIMPLE_STATE with type token = Token.t) : sig
  include
    STATE_WITH_LOCATION
      with type token = Token.t
       and type location = Location.t

  val initial : ?last_location:Location.t -> State.t -> t
end = struct
  type location = Location.t

  type token = Token.t

  type t =
    { inner_state : State.t
    ; last_location : Location.t option
    }

  let initial ?last_location inner_state = { inner_state; last_location }

  let[@inline] enable_backtracking s =
    let inner_state = State.enable_backtracking s.inner_state in
    { s with inner_state }

  let[@inline] disable_backtracking s =
    let inner_state = State.disable_backtracking s.inner_state in
    { s with inner_state }

  let[@inline] observe s =
    let open Option in
    State.observe s.inner_state >>= fun (t, inner_state') ->
    let location = Token.location t in
    let s' =
      { inner_state = inner_state'; last_location = Option.some location }
    in
    Option.some (t, s')

  let can_backtrack ~from ~to_ =
    State.can_backtrack ~from:from.inner_state ~to_:to_.inner_state

  let next_location s =
    let open Option in
    observe s $> fun (token, _s') -> Token.location token

  let previous_location s = s.last_location
end

module Make_simple_parser (Token : sig
  type t
end) (State : sig
  include SIMPLE_STATE with type token = Token.t
end) :
  PARSER
    with type token = Token.t
     and type state = State.t
     and type input = Token.t Seq.t = struct
  type token = Token.t

  type input = Token.t Seq.t

  type state = State.t

  type +'a t = State.t -> State.t * ('a, exn) result

  type 'a parser = 'a t

  let[@inline] run p s = p s

  let[@inline] run_exn p s =
    match run p s with
    | s', Result.Ok e -> (s', e)
    | _s', Result.Error cause -> raise cause

  let catch p handler s = run p s |> handler

  let fail e s = (s, Result.error e)

  let fail_at s e = fail e s

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

  exception
    Shifted_exception of
      { cause : exn
      ; path : exn list
      }

  exception
    Labelled_exception of
      { label : string
      ; cause : exn
      }

  let label p label =
    catch p (function
      | s, Result.Error cause ->
          fail_at s (Labelled_exception { cause; label })
      | x -> x)

  let labelled s p = label p s

  let shift p l =
    catch (label p l) (function
      | s, Result.Error cause ->
          fail_at s (Shifted_exception { cause; path = [] })
          (* FIXME: Path is never not [[]]. *)
      | x -> x)

  let shifted s p = shift p s

  let renamed label p =
    catch p (function
      | s, Result.Error (Labelled_exception { cause; _ }) ->
          fail_at s (Labelled_exception { label; cause })
      | s, Result.Error cause ->
          fail_at s (Labelled_exception { label; cause })
      | x -> x)

  let rec traverse f xs =
    match xs with
    | [] -> return []
    | x :: xs -> seq2 (f x) (traverse f xs) $> fun (x, xs) -> x :: xs

  let rec traverse_void f xs =
    match xs with
    | [] -> return ()
    | x :: xs -> f x &> traverse_void f xs

  let sequence ps = traverse Fun.id ps

  let trying p s =
    match run p s with
    | s, (Result.Error _ as e) ->
        let s' = State.enable_backtracking s in
        (s', e)
    | x -> x

  let alt p1 p2 s =
    match run p1 s with
    | s', Result.Error _ when State.can_backtrack ~from:s' ~to_:s -> run p2 s
    | x -> x

  exception No_more_choices of exn list

  let choice ps s =
    let rec go es = function
      | [] -> fail (No_more_choices es)
      | p :: ps' ->
          catch p (function
            | s', Result.Error e when State.can_backtrack ~from:s' ~to_:s ->
                run (go (e :: es) ps') s
            | x -> x)
    in
    run (go [] ps) s

  let maybe p =
    shifted "optionally" (alt (p $> Option.some) (return Option.none))

  let maybe_default p ~default = maybe p $> Option.value ~default

  let void p = p $> fun _ -> ()

  let rec many' p = alt (some' p $> List1.to_list) (return [])

  and some' p =
    let* x = p in
    let* xs = many' p in
    return (List1.from x xs)

  let many p = shifted "many" (many' p)

  let some p = shifted "some" (some' p)

  let sep_by0 p sep =
    maybe p
    >>= (function
          | Option.None -> return []
          | Option.Some x ->
              let* xs = many' (sep &> p) in
              return (x :: xs))
    |> shifted "many separated"

  let sep_by1 p sep =
    seq2 p (many' (sep &> p))
    $> (fun (x, xs) -> List1.from x xs)
    |> shifted "some separated"

  exception Expected_end_of_input

  let eoi =
    (fun s ->
      match State.observe s with
      | Option.None -> return_at s ()
      | Option.Some _ -> fail_at s Expected_end_of_input)
    |> labelled "end of input"

  let only p = p <& eoi

  exception Unexpected_end_of_input

  let satisfy f s =
    match State.observe s with
    | Option.None -> fail_at s Unexpected_end_of_input
    | Option.Some (x, s') -> (
        match f x with
        | Result.Ok _ as r -> (s', r)
        | Result.Error _ as r -> (s, r))

  (* TODO: [peek], [peekn] and [peek_satisfy] *)
end

module Make_parser_with_locations (Location : sig
  type t

  val join : t -> t -> t

  val[@warning "-32"] raise_at : t List1.t -> exn -> 'a
end) (Token : sig
  type t
end) (State : sig
  include
    STATE_WITH_LOCATION
      with type token = Token.t
       and type location = Location.t
end) : sig
  include
    PARSER
      with type token = Token.t
       and type state = State.t
       and type input = Token.t Seq.t

  val span : 'a t -> (Location.t * 'a) t
end = struct
  type token = Token.t

  type input = Token.t Seq.t

  type state = State.t

  type +'a t = State.t -> State.t * ('a, exn) result

  type 'a parser = 'a t

  let[@inline] run p s = p s

  let[@inline] run_exn p s =
    match run p s with
    | s', Result.Ok e -> (s', e)
    | _s', Result.Error cause -> raise cause

  let catch p handler s = run p s |> handler

  let fail e s = (s, Result.error e)

  let fail_at s e = fail e s

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

  exception
    Shifted_exception of
      { cause : exn
      ; path : exn list
      }

  exception
    Labelled_exception of
      { label : string
      ; cause : exn
      }

  let label p label =
    catch p (function
      | s, Result.Error cause ->
          fail_at s (Labelled_exception { cause; label })
      | x -> x)

  let labelled s p = label p s

  let shift p l =
    catch (label p l) (function
      | s, Result.Error cause ->
          fail_at s (Shifted_exception { cause; path = [] })
          (* FIXME: Path is never not [[]]. *)
      | x -> x)

  let shifted s p = shift p s

  let renamed label p =
    catch p (function
      | s, Result.Error (Labelled_exception { cause; _ }) ->
          fail_at s (Labelled_exception { label; cause })
      | s, Result.Error cause ->
          fail_at s (Labelled_exception { label; cause })
      | x -> x)

  let rec traverse f xs =
    match xs with
    | [] -> return []
    | x :: xs -> seq2 (f x) (traverse f xs) $> fun (x, xs) -> x :: xs

  let rec traverse_void f xs =
    match xs with
    | [] -> return ()
    | x :: xs -> f x &> traverse_void f xs

  let sequence ps = traverse Fun.id ps

  let trying p s =
    match run p s with
    | s, (Result.Error _ as e) ->
        let s' = State.enable_backtracking s in
        (s', e)
    | x -> x

  let alt p1 p2 s =
    match run p1 s with
    | s', Result.Error _ when State.can_backtrack ~from:s' ~to_:s -> run p2 s
    | x -> x

  exception No_more_choices of exn list

  let choice ps s =
    let rec go es = function
      | [] -> fail (No_more_choices es)
      | p :: ps' ->
          catch p (function
            | s', Result.Error e when State.can_backtrack ~from:s' ~to_:s ->
                run (go (e :: es) ps') s
            | x -> x)
    in
    run (go [] ps) s

  let maybe p =
    shifted "optionally" (alt (p $> Option.some) (return Option.none))

  let maybe_default p ~default = maybe p $> Option.value ~default

  let void p = p $> fun _ -> ()

  let rec many' p = alt (some' p $> List1.to_list) (return [])

  and some' p =
    let* x = p in
    let* xs = many' p in
    return (List1.from x xs)

  let many p = shifted "many" (many' p)

  let some p = shifted "some" (some' p)

  let sep_by0 p sep =
    maybe p
    >>= (function
          | Option.None -> return []
          | Option.Some x ->
              let* xs = many' (sep &> p) in
              return (x :: xs))
    |> shifted "many separated"

  let sep_by1 p sep =
    seq2 p (many' (sep &> p))
    $> (fun (x, xs) -> List1.from x xs)
    |> shifted "some separated"

  let next_location = get_state $> State.next_location

  let previous_location = get_state $> State.previous_location

  let span p =
    let* l1_opt = next_location
    and* x = p
    and* l2_opt = previous_location in
    match (l1_opt, l2_opt) with
    | Option.None, Option.Some l2 -> return (l2, x)
    | Option.Some l1, Option.Some l2 ->
        let l = Location.join l1 l2 in
        return (l, x)
    | _ ->
        assert
          false (* The parser [p] succeeded, so [l2_opt <> Option.none]. *)

  (*= TODO: let fail_at s error = fail_at' s (next_loc_at s) [] error *)

  exception Expected_end_of_input

  let eoi =
    (fun s ->
      match State.observe s with
      | Option.None -> return_at s ()
      | Option.Some _ -> fail_at s Expected_end_of_input)
    |> labelled "end of input"

  let only p = p <& eoi

  exception Unexpected_end_of_input

  let satisfy f s =
    match State.observe s with
    | Option.None -> fail_at s Unexpected_end_of_input
    | Option.Some (x, s') -> (
        match f x with
        | Result.Ok _ as r -> (s', r)
        | Result.Error _ as r -> (s, r))
end

module Make (Location : sig
  type t

  val join : t -> t -> t

  val raise_at : t List1.t -> exn -> 'a
end) (Token : sig
  type t

  val location : t -> Location.t
end) : sig
  include PARSER with type token = Token.t and type input = Token.t Seq.t

  val span : 'a t -> (Location.t * 'a) t

  val initial_state : ?last_location:Location.t -> input -> state
end = struct
  module Simple_state = Make_simple_state (Token)
  module State_with_locations =
    Make_location_state (Location) (Token) (Simple_state)
  module State = State_with_locations
  include Make_parser_with_locations (Location) (Token) (State)

  let initial_state ?last_location input =
    State_with_locations.initial ?last_location (Simple_state.initial input)
end

module Shunting_yard = Shunting_yard
