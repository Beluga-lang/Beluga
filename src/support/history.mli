
(** A history of items.

    A history contains a "past" and a "future". The history's state
    maintains its position in this sequence.
    A history supports moving back in time and forwards again as
    inverse operations.
    Histories support appending new items. Doing so when having
    shifted into the past creates a new "timeline", dropping the old
    future.
 *)
type 'a t

(** Creates an empty history. *)
val create : unit -> 'a t

(** Records a new entry in the history.
    If the history is in the past, then the future items are
    deleted by this action, thus creating a new "timeline".
 *)
val add : 'a t -> 'a -> unit

module Direction : sig
  type t =
    [ `forward
    | `backward
    ]

  (** Gets the inverse of a direction. *)
  val inverse : t -> t
end

(** Moves forward or backward in the history by one step.
    This shifts the last recorded item in the history's future or past
    into the past or future, respectively.
    The item that is shifted is returned, if the operation is possible.

    Invariant:
    If `step d h = Some x`, then executing `step (Direction.inverse d)
    h` brings the history back to the state it was in before.
 *)
val step : Direction.t -> 'a t -> 'a option

(** Converts the history to a pair of lists.
    The first list represents the past items. The second list
    represents the future items.
    Both lists have the most recent item first.
 *)
val to_lists : 'a t -> 'a list * 'a list
