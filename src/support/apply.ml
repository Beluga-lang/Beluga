module type APPLY = sig
  type 'a t

  val ap : 'a t -> ('a -> 'b) t -> 'b t

  val ( <&> ) : ('a -> 'b) t -> 'a t -> 'b t

  val ap_first : 'b t -> 'a t -> 'a t

  val ( <& ) : 'a t -> 'b t -> 'a t

  val ap_second : 'b t -> 'a t -> 'b t

  val ( &> ) : 'a t -> 'b t -> 'b t

  val seq2 : 'a1 t -> 'a2 t -> ('a1 * 'a2) t

  val seq3 : 'a1 t -> 'a2 t -> 'a3 t -> ('a1 * 'a2 * 'a3) t

  val seq4 : 'a1 t -> 'a2 t -> 'a3 t -> 'a4 t -> ('a1 * 'a2 * 'a3 * 'a4) t

  val seq5 :
       'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'a5 t
    -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5) t

  val replicate : int -> 'a t -> 'a list t
end

module Make (M : Monad.MONAD) : APPLY with type 'a t = 'a M.t = struct
  include M

  let[@inline] ap a f =
    a >>= fun a ->
    f >>= fun f -> return (f a)

  let[@inline] ( <&> ) f a = ap a f

  let[@inline] ap_first m2 m1 = m1 >>= fun x -> m2 >>= Fun.const (return x)

  let[@inline] ( <& ) m1 m2 = ap_first m2 m1

  let[@inline] ap_second m2 m1 = m1 >>= fun _ -> m2 >>= return

  let[@inline] ( &> ) m1 m2 = ap_second m2 m1

  let[@inline] seq2 m1 m2 =
    m1 >>= fun x1 ->
    m2 >>= fun x2 -> return (x1, x2)

  let[@inline] seq3 m1 m2 m3 =
    m1 >>= fun x1 ->
    m2 >>= fun x2 ->
    m3 >>= fun x3 -> return (x1, x2, x3)

  let[@inline] seq4 m1 m2 m3 m4 =
    m1 >>= fun x1 ->
    m2 >>= fun x2 ->
    m3 >>= fun x3 ->
    m4 >>= fun x4 -> return (x1, x2, x3, x4)

  let[@inline] seq5 m1 m2 m3 m4 m5 =
    m1 >>= fun x1 ->
    m2 >>= fun x2 ->
    m3 >>= fun x3 ->
    m4 >>= fun x4 ->
    m5 >>= fun x5 -> return (x1, x2, x3, x4, x5)

  let replicate =
    let rec replicate n a =
      if n = 0 then return []
      else
        a >>= fun x ->
        replicate (n - 1) a >>= fun xs -> return (List.cons x xs)
    in
    fun n ->
      if n < 0 then raise @@ Invalid_argument "replicate" else replicate n
end
