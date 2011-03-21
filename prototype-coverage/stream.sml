(* Stream library *)
(* Author: Frank Pfenning *)
(* Some anonymous modifications *)

signature STREAM =
sig

  type 'a stream
  datatype 'a front = Nil | Cons of 'a * 'a stream

  val force : 'a stream -> 'a front
  val delay : (unit -> 'a front) -> 'a stream

  val empty : 'a stream

  val null : 'a stream -> bool
  val hd : 'a stream -> 'a		(* may raise Empty *)
  val tl : 'a stream -> 'a stream	(* may raise Empty *)   
  val append : 'a stream * 'a stream -> 'a stream
  val map : ('a -> 'b) -> 'a stream -> 'b stream

  val app : ('a -> unit) -> 'a stream -> unit

  val filter : ('a -> bool) -> 'a stream -> 'a stream

  val take : 'a stream * int -> 'a list (* may raise Subscript *)
  val drop : 'a stream * int -> 'a stream (* may raise Subscript *)

  val tabulate : (int -> 'a) -> 'a stream
                                
end;  (* signature STREAM *)

structure Stream :> STREAM = struct

  (*
   type 'a susp = unit -> 'a
   datatype 'a front = Nil | Cons of 'a * 'a stream
   withtype 'a stream = ('a front) susp
   *)
  datatype 'a front = Nil | Cons of 'a * (unit -> 'a front)
  type 'a stream = unit -> 'a front

  fun force s = s()
  fun delay s =
      let 
        exception Impossible
        val memo = ref (fn () => raise Impossible)
        fun s'() =  (* executed only once... *)
            let 
              val r = s() 
            in 
              memo := (fn () => r); 
              r 
            end
      in
        memo := s';
        fn () => (!memo)()
      end

  val empty = (fn () => Nil)

  (* functions null, hd, tl, map, filter, take, drop *)
  (* parallel the functions in the List structure *)
  fun null' (Nil) = true
    | null' (Cons _) = false
  fun null s = null' (force s)

  fun hd' (Nil) = raise Empty
    | hd' (Cons (x,s)) = x
  fun hd s = hd' (force s)

  fun tl' (Nil) = raise Empty
    | tl' (Cons (x,s)) = s
  fun tl s = tl' (force s) 

  fun append (s, t) = delay (fn () => append'(force s,t))
  and append' (Nil, t) = force t
    | append' (Cons(x,s), t) = Cons(x, append(s,t)) 

  fun map f s = delay (fn () => map' f (force s))
  and map' f (Nil) = Nil
    | map' f (Cons(x,s)) = Cons (f(x), map f s)

  fun app f s =
      case force s
       of Nil => ()
        | Cons(a,s) => (f a; app f s)

  fun filter p s = delay (fn () => filter' p (force s))
  and filter' p (Nil) = Nil
    | filter' p (Cons(x,s)) =
      if p(x) then Cons (x, filter p s)
      else filter' p (force s)

  (* take (s,n) converts the first n elements of n to a list *)
  (* raises Subscript if n < 0 or n >= length(s) *)
  fun takePos (s, 0) = nil
    | takePos (s, n) = take' (force s, n)
  and take' (Nil, _) = raise Subscript
    | take' (Cons(x,s), n) = x::takePos(s, n-1)
  fun take (s,n) = if n < 0 then raise Subscript else takePos (s,n)

  fun dropPos (s, 0) = s
    | dropPos (s, n) = drop' (force s, n)
  and drop' (Nil, _) = raise Subscript
    | drop' (Cons(x,s), n) = dropPos (s, n-1)
  fun drop (s, n) = if n < 0 then raise Subscript else dropPos (s,n)

  fun tabulate f = delay (fn () => tabulate' f)
  and tabulate' f = Cons (f(0), tabulate (fn i => f(i+1)))

end;  (* structure Stream *)
