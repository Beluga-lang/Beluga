module type STATE = sig
  type state

  include Monad.MONAD with type 'a t = state -> state * 'a

  val get : state t

  val put : state -> unit t

  val modify : (state -> state) -> unit t

  val run : 'a t -> state -> state * 'a

  val eval : 'a t -> state -> 'a

  val locally : (state -> state) -> 'a t -> 'a t

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

module Make (S : sig
  type t
end) : STATE with type state = S.t = struct
  module State = struct
    type state = S.t

    let[@inline] run m init = m init

    let[@inline] eval m init =
      let _final, n = run m init in
      n

    let[@inline] locally f m s =
      let a = eval m (f s) in
      (s, a)

    include Monad.Make (struct
      (** The type of state transformers. *)
      type 'a t = state -> state * 'a

      let[@inline] return a state = (state, a)

      let[@inline] bind f v state =
        let state', a = run v state in
        f a state'
    end)

    let[@inline] get state = (state, state)

    let[@inline] put state' _m = (state', ())

    let[@inline] modify f =
      get >>= fun s ->
      let s' = f s in
      put s'
  end

  include State
  include Functor.Make (State)
  include Apply.Make (State)
end
