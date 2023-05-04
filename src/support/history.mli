(** A history of items.

    A history is a mutable data structure that keeps track of its "past" and
    "future". The history's state maintains its position in this sequence. A
    history supports moving back in time and forwards again as inverse
    operations.

    Histories support appending new items. Doing so when having shifted into
    the past creates a new "timeline", dropping the old future. *)
type 'a t

(** Creates an empty history. *)
val create : unit -> 'a t

(** Records a new entry in the history. If the history is in the past, then
    the future items are deleted by this action, thus creating a new
    "timeline". *)
val add : 'a t -> 'a -> unit

(** [step_forward history] steps the history forward, and yields [history]'s
    future if it exists. *)
val step_forward : 'a t -> 'a option

(** [step_backward history] steps the history backward, and yields
    [history]'s past if it exists. *)
val step_backward : 'a t -> 'a option

(** Converts the history to a pair of lists. The first list represents the
    past items. The second list represents the future items. Both lists have
    the most recent item first. *)
val to_lists : 'a t -> 'a list * 'a list
