(* COMP 302 Assignment 5
 * Sample Solution
 *)

signature SUBTYPE = sig

  (* subtype : tp * tp -> bool
   * subtype(t1, t2) returns true iff ANY subtyping rule can be successfully
   *  applied to derive the judgment that t1 is a subtype of t2.
   *)
  val subtype : MinML.tp * MinML.tp -> bool

end


structure Subtype :> SUBTYPE = struct

  open Type

  exception Unimplemented

  (* Q1: 40 points *)

  (* subtypeOrd : tp * tp -> bool
   * Returns true iff any subtyping rule EXCEPT for refl, &-left-1, &-left-2, &-right
   *  can be successfully applied.
   * (``Ord'' = ``ordinary'' subtyping, that is, not with intersection types.)
   * 
   * NOTE: do NOT call subtypeOrd directly from inside subtypeOrd --
   *  call subtype instead!
   *)
  fun subtypeOrd (t1, t2) = case (t1, t2) of
      (* Rule `arrow' *)
        (Arrow(domain1, range1), Arrow(domain2, range2)) =>
           subtype(domain2, domain1) andalso subtype(range1, range2)
      
      (* Rule `product' *)
      | (Product tps1, Product tps2) =>
           (* HINT: call List.all and ListPair.zip *)
           List.length tps1 = List.length tps2 andalso List.all subtype (ListPair.zip (tps1, tps2))
      
      (* Rule `base-int' *)
      | (Int, Real) => true
      
      (* Rules `cond-left', `cond-right' *)
      | (_, _) => false
       
  (* sectR : tp * tp -> bool
   * Returns true iff the ``&-right'' rule can be successfully applied.
   *)
  and sectR (_, _) = false

  (* sectLs : tp * tp -> bool
   * Returns true iff the ``&-left-1'' rule OR the ``&-left-2'' rule
   *  can be successfully applied.
   *)
  and sectLs (_, _) = false

  (* subtype : tp * tp -> bool
   * Returns true iff ANY subtyping rule can be successfully applied.
   *)
  and subtype (t1, t2) =
        eq(t1, t2)
      orelse
        subtypeOrd (t1, t2)
      orelse
        sectLs (t1, t2)
      orelse
        sectR (t1, t2)

end
