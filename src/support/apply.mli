(** Module type for abstract datatypes with applicable actions and sequential
    applications. *)
module type APPLY = sig
  type 'a t

  (** [ap fa fab] applies argument [fa] to [fab] under the abstract datatype
      {!type:t}. *)
  val ap : 'a t -> ('a -> 'b) t -> 'b t

  (** [( <&> )] is an infix synonym of {!ap}. *)
  val ( <&> ) : ('a -> 'b) t -> 'a t -> 'b t

  (** {1 Combinators} *)

  (** [ap_first second first] combines actions [first] and [second] but keeps
      only [first]. That is, [ap_first second first = first]. The order of
      arguments is for use in function pipelines as
      [first = first |> ap_first second]. *)
  val ap_first : 'b t -> 'a t -> 'a t

  (** [( <& )] is an infix synonym for {!ap_first}. *)
  val ( <& ) : 'a t -> 'b t -> 'a t

  (** [ap_second second first] combines actions [first] and [second] but
      keeps only [second]. That is, [ap_second second first = second]. The
      order of arguments is for use in function pipelines as
      [second = first |> ap_second second]. *)
  val ap_second : 'b t -> 'a t -> 'b t

  (** [( &> )] is an infix synonym for {!ap_second}. *)
  val ( &> ) : 'a t -> 'b t -> 'b t

  (** [seq2 fa1 fa2] sequentially executes actions [fa1] and [fa2], and keeps
      their outputs under the abstract datatype {!type:t}. *)
  val seq2 : 'a1 t -> 'a2 t -> ('a1 * 'a2) t

  (** [seq3 fa1 fa2 fa3] sequentially executes actions [fa1], [fa2] and
      [fa3], and keeps their outputs under the abstract datatype {!type:t}. *)
  val seq3 : 'a1 t -> 'a2 t -> 'a3 t -> ('a1 * 'a2 * 'a3) t

  (** [seq4 fa1 fa2 fa3 fa4] sequentially executes actions [fa1], [fa2],
      [fa3] and [fa4], and keeps their outputs under the abstract datatype
      {!type:t}. *)
  val seq4 : 'a1 t -> 'a2 t -> 'a3 t -> 'a4 t -> ('a1 * 'a2 * 'a3 * 'a4) t

  (** [seq5 fa1 fa2 fa3 fa4 fa5] sequentially executes actions [fa1], [fa2],
      [fa3], [fa4] and [fa5], and keeps their outputs under the abstract
      datatype {!type:t}. *)
  val seq5 :
       'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'a5 t
    -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5) t

  (** [lift2 f ma1 ma2] sequentially executes actions [ma1], [ma2] and passes
      their outputs to [f]. *)
  val lift2 : ('a1 -> 'a2 -> 'r) -> 'a1 t -> 'a2 t -> 'r t

  (** [lift3 f ma1 ma2 ma3] sequentially executes actions [ma1], [ma2], [ma3]
      and passes their outputs to [f]. *)
  val lift3 : ('a1 -> 'a2 -> 'a3 -> 'r) -> 'a1 t -> 'a2 t -> 'a3 t -> 'r t

  (** [lift4 f ma1 ma2 ma3 ma4] sequentially executes actions [ma1], [ma2],
      [ma3], [ma4] and passes their outputs to [f]. *)
  val lift4 :
       ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'r)
    -> 'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'r t

  (** [lift5 f ma1 ma2 ma3 ma4 ma5] sequentially executes actions [ma1],
      [ma2], [ma3], [ma4], [ma5] and passes their outputs to [f]. *)
  val lift5 :
       ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'r)
    -> 'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'a5 t
    -> 'r t

  (** [replicate n a] sequentially runs [n] times [a].

      @raise Invalid_argument If [n < 0]. *)
  val replicate : int -> 'a t -> 'a list t
end

(** Functor building an implementation of {!APPLY} over a monad. *)
module Make (M : Monad.MONAD) : APPLY with type 'a t = 'a M.t
