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

  (** [replicate n a] sequentially runs [n] times [a].

      @raise Invalid_argument If [n < 0]. *)
  val replicate : int -> 'a t -> 'a list t
end

(** Functor building an implementation of {!APPLY} over a monad. *)
module Make (M : Monad.MONAD) : APPLY with type 'a t = 'a M.t
