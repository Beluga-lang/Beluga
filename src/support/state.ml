module type STATE = sig
  type state

  include Monad.MONAD with type 'a t = state -> state * 'a

  val get : state t

  val put : state -> unit t

  val run : 'a t -> init:state -> state * 'a

  include Functor.FUNCTOR with type 'a t := 'a t

  include Apply.APPLY with type 'a t := 'a t
end

module Make (S : sig
  type t
end) : STATE with type state = S.t = struct
  module State = struct
    type state = S.t

    let run m ~init = m init

    include Monad.Make (struct
      (** The type of state transformers. *)
      type 'a t = state -> state * 'a

      let return a state = (state, a)

      let bind f v state =
        let state', a = run ~init:state v in
        f a state'
    end)

    let get state = (state, state)

    let put state' _ = (state', ())
  end

  include State
  include Functor.Make (State)
  include Apply.Make (State)
end
