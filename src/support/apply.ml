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

  val lift2 : ('a1 -> 'a2 -> 'r) -> 'a1 t -> 'a2 t -> 'r t

  val lift3 : ('a1 -> 'a2 -> 'a3 -> 'r) -> 'a1 t -> 'a2 t -> 'a3 t -> 'r t

  val lift4 :
       ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'r)
    -> 'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'r t

  val lift5 :
       ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'r)
    -> 'a1 t
    -> 'a2 t
    -> 'a3 t
    -> 'a4 t
    -> 'a5 t
    -> 'r t

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
    let* x1 = m1
    and* x2 = m2 in
    return (x1, x2)

  let[@inline] seq3 m1 m2 m3 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3 in
    return (x1, x2, x3)

  let[@inline] seq4 m1 m2 m3 m4 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3
    and* x4 = m4 in
    return (x1, x2, x3, x4)

  let[@inline] seq5 m1 m2 m3 m4 m5 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3
    and* x4 = m4
    and* x5 = m5 in
    return (x1, x2, x3, x4, x5)

  let[@inline] lift2 f m1 m2 =
    let* x1 = m1
    and* x2 = m2 in
    return (f x1 x2)

  let[@inline] lift3 f m1 m2 m3 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3 in
    return (f x1 x2 x3)

  let[@inline] lift4 f m1 m2 m3 m4 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3
    and* x4 = m4 in
    return (f x1 x2 x3 x4)

  let[@inline] lift5 f m1 m2 m3 m4 m5 =
    let* x1 = m1
    and* x2 = m2
    and* x3 = m3
    and* x4 = m4
    and* x5 = m5 in
    return (f x1 x2 x3 x4 x5)

  let replicate =
    let rec replicate n a =
      if n = 0 then return []
      else
        let* x = a in
        let* xs = replicate (n - 1) a in
        return (List.cons x xs)
    in
    fun n ->
      if n < 0 then raise (Invalid_argument "replicate") else replicate n
end
