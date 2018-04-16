(** Essentially a list, but that tracks its length as items are added and removed. *)
type 'a t

(** Constructs an empty stack. *)
val empty : 'a t

(** Gets the length of the stack in O(1). *)
val length : 'a t -> int

(** Converts the stack to a list. *)
val to_list : 'a t -> 'a list

(** Decides whether a stack is empty. *)
val is_empty : 'a t -> bool

(** Pushes an item onto the stack. *)
val push : 'a -> 'a t -> 'a t

(** Pops an item from the stack. *)
val pop : 'a t -> ('a * 'a t) Maybe.t

(** Tries to pop `n` items from a stack, yielding them in a list.
The elements are collected in _reverse order_, so the old top of the
stack is the last element of the returned list. *)
val cut : int -> 'a t -> ('a list * 'a t) Maybe.t
