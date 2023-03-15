(** Persistent association tables over hashable types.

    The module implements Hash Array Mapped Trie.

    @author Thibault Suzanne *)

(** Input signature of the size configuration of the structure. *)
module type CONFIG = sig
  (** The number of bits taken from the hashed key at every step of an
      elementary function. Note that [2 ^ (2 ^ shift_step)] {b must} be a
      valid OCaml [int] on the considered architecture (the bigger the
      better). *)
  val shift_step : int

  (** Arbitrary. It is used to balance time and space consumption. A good
      value seems to be [2 ^ shift_step - 1]. *)
  val bmnode_max : int

  (** Arbitrary. Must be lesser than [bmnode_max]. A good value seems to be
      [bmnode_max / 2]. *)
  val arrnode_min : int
end

(** Standard configuration for 64-bits architectures. Its parameters are :

    {[
      let shift_step = 5

      let bmnode_max = 16

      let arrnode_min = 8
    ]} *)
module StdConfig : CONFIG

(** Standard configuration for 32-bits architectures. Its parameters are :

    {[
      let shift_step = 4

      let bmnode_max = 8

      let arrnode_min = 4
    ]} *)
module StdConfig32 : CONFIG

module type S = sig
  (** Output signature of the {!Make} module. *)

  (** The type of the Hamt keys. *)
  type key

  (** The type of tables from type [key] to type ['a]. *)
  type 'a t

  (** The empty table. *)
  val empty : 'a t

  (** Tests whether a table is empty or not. *)
  val is_empty : 'a t -> bool

  (** Creates a new table with a single binding. *)
  val singleton : key -> 'a -> 'a t

  (** Returns the number of bindings of a table. *)
  val cardinal : 'a t -> int

  (** alias of [cardinal] *)
  val length : 'a t -> int

  (** {3 Modify bindings} *)

  (** [update k f t] adds, modifies or deletes the binding from the key [k]
      in [t], returning the new table. If such a binding exists in [t] to a
      value [v], [f] is given [Some v], otherwise [None]. The presence of the
      binding from [k] in the result is determined the same way by [f]. *)
  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t

  (** Adds a binding to a map, returning the new map. If the binding already
      existed, the older one disappears. *)
  val add : key -> 'a -> 'a t -> 'a t

  (** [add_carry k v t] adds a binding to [t], returning the new table and
      optionnally the value previously bound to [k]. *)
  val add_carry : key -> 'a -> 'a t -> 'a t * 'a option

  (** Removes a binding from a table, returning the new table. *)
  val remove : key -> 'a t -> 'a t

  (** {!extract}, {!update} and {!modify} raise [Not_found] if the
      corresponding binding is not present in their table parameter. *)

  (** [extract k t] removes the binding with the key [k] from [t], returning
      the value previously bound from [k] and the new table. *)
  val extract : key -> 'a t -> 'a * 'a t

  (** [alter k f t] updates the binding from [k] in [t], optionnally deleting
      it, and returns the new table. *)
  val alter : key -> ('a -> 'a option) -> 'a t -> 'a t

  (** [modify k f t] modifies the binding from [k] in [t], and returns the
      new table. *)
  val modify : key -> ('a -> 'a) -> 'a t -> 'a t

  (** [modify_def v0 k f t] modifies the binding from [k] in [t]. If no value
      is bound from [k], the default one [v0] is used by [f]. *)
  val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> 'a t

  (** {3 Getting elements} *)

  (** [find k t] returns the value bound from the key [k] in [t]. If there is
      no such binding, [Not_found] is raised. *)
  val find : key -> 'a t -> 'a

  val find_opt : key -> 'a t -> 'a option

  (** Checks for the presence of a binding from a key in a table. *)
  val mem : key -> 'a t -> bool

  (** Returns a binding from a table, which one is unspecified. If the table
      is [Empty], raises [Not_found]. *)
  val choose : 'a t -> key * 'a

  (** Returns a binding from a table, which one is unspecified. If the table
      is [Empty], raises [Not_found]. *)
  val choose_opt : 'a t -> (key * 'a) option

  (** Removes a binding from a table, returning a pair constituted of this
      binding and the table without it. If the table is [Empty], raises
      [Not_found]. *)
  val pop : 'a t -> (key * 'a) * 'a t

  (** {3 Iterators} *)

  (** Returns the list of the keys of a table (order unspecified). *)
  val keys : 'a t -> key list

  (** Returns the list of the values of a table (order unspecified). *)
  val values : 'a t -> 'a list

  (** Returns the list of the bindings [(key, value)] of a table (order
      unspecified). *)
  val bindings : 'a t -> (key * 'a) list

  val to_seq : 'a t -> (key * 'a) Seq.t

  val of_seq : (key * 'a) Seq.t -> 'a t

  (** Iterates the application of a function over the bindings of a table. *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit

  (** [map f t] returns the table with the same keys as [t], where all value
      [v] in [t] has been replaced by [f v].*)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** [mapi f t] returns the table with the same keys as [t], where all value
      [v] of [t] bound from the key [k] has been replaced by [f k v]. *)
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

  (** [filterv f t] returns a table whose bindings are the bindings of [t] to
      a value [v] where [f v = true]. *)
  val filterv : ('a -> bool) -> 'a t -> 'a t

  (** [filter f t] returns a table whose bindings are the bindings of t from
      a key [k] to a value [v] where [f k v = true]. *)
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t

  (** Combines the features of [filter] and [map]. [filter_map f t] returns a
      table where there is a binding from a key [k] to a value [v] if and
      only if there is a binding from [k] to a value [w] in [t] where
      [f k w = Some v]. *)
  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t

  (** [fold f t x] computes [(f vN ... (f v1 (f v0 x)))] where
      [v0, v1, ..., vN] are the values bound in [t], provided in unspecified
      order. *)
  val foldv : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** [fold f t x] computes [(f kN vN ... (f k1 v1 (f k0 v0 x)))] where
      [k0, k1, ..., kN] are the keys of [t] and [v0, v1, ..., vN] the values
      associated to these keys. The order in which the bindings are provided
      to [f] is unspecified. *)
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** {5 Scanning} *)

  (** [for_all f t] returns [true] if [f k v] is [true] for all binding from
      [k] to [v] in [t], [false] otherwise. *)
  val for_all : (key -> 'a -> bool) -> 'a t -> bool

  (** [exists f t] returns [true] if [f k v] is [true] for at least one
      binding from [k] to [v] in [t], [false] otherwise. *)
  val exists : (key -> 'a -> bool) -> 'a t -> bool

  (** [partition f t] returns a pair [(t1, t2)] where [t1] is composed of the
      bindings of [t] satisfying the predicate [f], and [t2] of the bindings
      which do not. *)
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

  (** {3 Merging} *)

  (** [intersecti f t1 t2] returns a table with bindings only from keys [k]
      found in [t1] and [t2], and to values [v = f k v1 v2] if [k] is bound
      to [v1] in [t1] and to [v2] in [t2]. *)
  val intersecti : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** [intersecti f t1 t2] returns a table with bindings only from keys [k]
      found in [t1] and [t2], and to values [v = f v1 v2] if [k] is bound to
      [v1] in [t1] and to [v2] in [t2]. *)
  val intersect : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** [merge f t1 t2] returns a table whose keys is a subset of the keys of
      [t1] and [t2]. The presence in the result of each such binding, and its
      corresponding value, are determined by the function [f]. *)
  val merge :
    (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

  (** [union f t1 t2] returns a table whose keys are all keys presents in
      [t1] or in [t2]. If a key [k] is present in only one table, the
      corresponding value is chosen in the result. If it is bound to [v1] in
      [t1] and [v2] in [t2], the value in the result is [f k v1 v2]. *)
  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  (** {2 Importing values from another structure} *)

  (** The [Import] module is used to transform a full big set of data into a
      Hamt. It uses internal mechanisms relying on the implementation of the
      Hamt structure to provide faster imports than adding the bindings of
      the imported structure element by element. However, if you want to
      import a data structure into a Hamt which is already a lot bigger, you
      should consider adding the elements with the usual fonctions of
      {!Make}. At which size difference the faster method is switched is not
      yet determined and must be analysed in your own case. *)

  module Import : sig
    (** Input signature of the module {!Make}, representing datas to be
        imported in Hamt. *)
    module type FOLDABLE = sig
      (** The type of your datas' keys. *)
      type key

      (** The type of your data structure with ['a]-typed values. *)
      type 'a t

      (** A fold function on your data structure. Its role is to apply a
          function to every binding of your structure, building the Hamt by
          accumulation on the third parameter of this function. *)
      val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    end

    module Make (M : FOLDABLE with type key = key) : sig
      (** [add_from s t] adds every binding of [s] to the Hamt [t]. *)
      val add_from : 'a M.t -> 'a t -> 'a t

      (** [from s] buils a Hamt containing every binding of [s].*)
      val from : 'a M.t -> 'a t
    end

    module AssocList : sig
      (** [add_from li t] adds every binding of the association list [li] to
          the Hamt t. *)
      val add_from : (key * 'a) list -> 'a t -> 'a t

      (** [from li] builds a Hamt containing every binding of the association
          list [li]. *)
      val from : (key * 'a) list -> 'a t
    end
  end
end

(** Functor building an implementation of the Hamt structure, given a
    hashable type. *)
module Make (Config : CONFIG) (Key : Hashtbl.HashedType) :
  S with type key = Key.t
[@@warning "-67"]

module Make' (Key : Hashtbl.HashedType) : S with type key = Key.t
