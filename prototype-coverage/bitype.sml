(*
* Name : Shen Chen Xu
* Id   : 260375681
*)
signature TYPECHECK = sig

  type context  (* Context of typing assumptions; example: x : int, p : bool *)
  val empty : context

  (* Synthesize a type from an expression, returning the type *)
  val synth : context -> MinML.exp -> Type.tp

  (* Check an expression against the type it's supposed to have*)
  val check : context -> MinML.exp -> Type.tp -> unit

  exception TypeError of string

end

structure Typecheck :> TYPECHECK = struct

  open Type
  structure M = MinML

  datatype context = Ctx of (M.name * tp) list

  val empty = Ctx []

  exception Unimplemented

  exception NotFound
  fun assoc x [] = raise NotFound
    | assoc x ((y, r)::rest) = if x = y then r else assoc x rest

  fun lookup (Ctx list) x = assoc x list
  fun extend (Ctx list) (x, v) = Ctx((x, v)::list)

  fun extend_list ctx [] = ctx
    | extend_list ctx ((x, v)::pairs) = extend_list (extend ctx (x, v)) pairs

  exception TypeError of string

  (* fail : string -> 'a
   *
   * Raises the TypeError exception, for ill-typed MinML programs.
   *)
  fun fail message = raise TypeError message

  fun primopType primop = case primop of
        M.Equals => Arrow(Product[Int, Int], Bool)
      | M.LessThan => Arrow(Product[Int, Int], Bool)
      | M.Plus => Arrow(Product[Int, Int], Int)
      | M.Minus => Arrow(Product[Int, Int], Int)
      | M.Times => Arrow(Product[Int, Int], Int)
      | M.Negate => Arrow(Int, Int)

  (* synth : context -> M.exp -> tp
   *
   * Synthesize a type from an expression.
   * Returns the synthesized (inferred) type if one exists;
   *   otherwise raises TypeError.
   *) 
  fun synth ctx exp = case exp of
      M.Int _ => Int
    | M.Bool _ => Bool
    | M.Primop(po, exps) =>
         let val poType as Arrow(domain, range) = primopType po
             val productizedExps = case exps of [one] => one
                                              | several => M.Tuple several
         in
           check ctx productizedExps domain;
           range
         end

    | M.Tuple es =>
         Product (List.map (synth ctx) es)

    (* Q3.2 *)
    | M.Apply (e1, e2) =>
        let
          val foo = synth ctx e1
        in
          case foo of
            Arrow(domain, range) => (check ctx e2 domain; range)
          | _ => fail "Applying a non-function"
        end
                            
    | M.Var x => lookup ctx x

    | M.Anno (e, t) =>
        (check ctx e t;
         t)

    | M.Rec (f, ftype, e) =>
         let val ctx_f = extend ctx (f, ftype)
         in
           (check ctx_f e ftype;
            ftype)
         end

    | M.Let(decs, exp) =>
      let val ctx_decs = bind ctx decs
      in
        synth ctx_decs exp
      end

    | M.Case (e, cs) => (* fail "Case: not implemented" *)
      let val t = synth ctx e
          val (patterns, clauses) = ListPair.unzip cs

          fun checkpat ctx p t =
              case (p, t) of
                (M.Varpat x, t) => [(x, t)]
              | (M.Intpat _, Int) => []
              | (M.Intpat _, _) => fail "115: Pattern type error"
              | (M.Boolpat _, Bool) => []
              | (M.Boolpat _, _) => fail "117: Pattern type error"
              | (M.Tuplepat ps, Product ts) =>
                if length ps = length ts then
                  foldl (fn ((p, t), bs) => (checkpat ctx p t) @ bs)
                        []
                        (ListPair.zip (ps, ts))
                else raise fail "123: Pattern type error"
              | (M.Tuplepat ps, t) => fail ("Fail to check pattern against " ^ Type.toString t)
              | (M.Valconpat (x, p), Tycon y) =>
                let val tp = lookup ctx x
                in
                  case tp of
                    Arrow (domain, Tycon range) =>
                    if range = y then
                      checkpat ctx p domain
                    else
                      fail "129: Pattern type error"
                  | _ => fail "130: Pattern type error"
                end
              | (M.Valconpat (x, p), _) => fail "130: Pattern type error"
              | (M.Valcon0pat x, Tycon y) =>
                let val tp = lookup ctx x
                in
                  case tp of
                    Tycon xt =>
                    if xt = y then [] else fail "135: Pattern type error"
                  | _ => fail "136: Pattern type error"
                end
              | (M.Valcon0pat _, _) => fail "138: Pattern type error"
          fun synthclause [] = []
            | synthclause ((p, e) :: cs) =
              (synth (extend_list ctx (checkpat ctx p t)) e) :: (synthclause cs)
          val clausesType = synthclause cs
      in
        if List.all (fn x => Type.eq (x, hd clausesType)) clausesType then
          hd clausesType
        else
          fail "Type of clauses don't agree"
      end
    
    | _ => fail "Can't synthesize type"

  (* check : context -> M.exp -> tp -> unit
   *
   * Check an expression against a type.
   * Returns () if it succeeds; otherwise raises TypeError.
   *) 
  and check ctx exp t = case (exp, t) of
      (* Q3.1 *)
      (M.If(e, e1, e2), t) =>
        (check ctx e Type.Bool; check ctx e1 t; check ctx e2 t)

    | (M.Tuple es, Product ts) =>
         if length es <> length ts then fail "tuple length mismatch"
         else List.app (fn (ei, ti) => check ctx ei ti) (ListPair.zip(es, ts))

    | (M.Fn(x, body), Arrow(domain, range)) =>
         let val ctx_x = extend ctx (x, domain)
         in
           check ctx_x body range
         end

    | (M.Let(decs, exp), t) =>
         let val ctx_decs = bind ctx decs
         in
           check ctx_decs exp t
         end

    | (e, t) =>
         let val synthesizedType = synth ctx e
         in
           if Type.eq (synthesizedType, t) then ()
           else fail ("Checking against " ^ Type.toString t
                    ^ ", but synthesized type " ^ Type.toString synthesizedType)
         end

  (* bind : context -> M.dec list -> context
   *
   * Synthesizes types for declarations, returning a context with appropriate
   *  new typing assumptions; or, if not type-correct, raises TypeError.
   *
   * This function implements the rules deriving  Gamma |- decs  up  Gamma'.
   *)
  and bind ctx [] = ctx
    | bind ctx (dec::rest) =
        let val ctx_dec =
                  case dec of
                    M.Val(e, x) => extend ctx (x, synth ctx e)

                  | M.Valtuple(e, xs) =>
                        let in case synth ctx e of
                                 Product ts =>
                                   if length ts <> length xs then fail "Valtuple length mismatch"
                                   else extend_list ctx (ListPair.zip (xs, ts))
                               | _ => fail "Valtuple"
                        end
                  | M.Datatype (t, vs) =>
                    let fun lst2tp [t] = t
                          | lst2tp ts = Product ts
                        fun bind_valcons ctx [] = ctx
                          | bind_valcons ctx (v::vs) =
                            let val ctx_dec =
                                    case v of
                                      (name, []) => extend ctx (name, Tycon t)
                                    | (name, a) => extend ctx (name, Arrow (lst2tp a, Tycon t))
                            in
                              bind_valcons ctx_dec vs
                            end
                    in
                      bind_valcons ctx vs
                    end
        in
          bind ctx_dec rest
        end
end
