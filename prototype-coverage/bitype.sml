(* TODO
 * - check if patterns are linear
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
  structure C = Coverage

  datatype context = Ctx of ((M.name * tp) list * C.dt list)

  val empty = Ctx ([], [])

  exception Unimplemented

  exception NotFound
  fun dtctx (Ctx (_, dts)) = dts
  fun assoc x [] = raise NotFound
    | assoc x ((y, r)::rest) = if x = y then r else assoc x rest

  fun lookup (Ctx (ts, _)) x = assoc x ts
  fun extend (Ctx (ts, dts)) (x, v) = Ctx ((x, v) :: ts, dts)
  fun extend_dt (Ctx (ts, dts)) dt  = Ctx (ts, dt :: dts)

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
  fun synth ctx exp =
      case exp of
        M.Int _ => Int
      | M.Bool _ => Bool
      | M.Valcon _ => fail "bitype.sml: 66"
      | M.Valcon0 _ => fail "bitype.sml: 67"
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

      | M.Case (e, cs) =>
        let val t = synth ctx e
            val (patterns, clauses) = ListPair.unzip cs
            fun checkpat ctx p t =
                case (p, t) of
                  (M.Varpat x, t) => [(x, t)]
                | (M.Intpat _, Int) => []
                | (M.Boolpat _, Bool) => []
                | (M.Tuplepat ps, Product ts) =>
                  if length ps = length ts then
                    foldl (fn ((p, t), bs) => (checkpat ctx p t) @ bs)
                          []
                          (ListPair.zip (ps, ts))
                  else
                    fail "Pattern of wrong type inside CASE expression"
                | (M.Valconpat (x, p), Tycon y) =>
                  let val tp = lookup ctx x
                  in
                    case tp of
                      Arrow (domain, Tycon range) =>
                      if range = y then
                        checkpat ctx p domain
                      else
                        fail "Pattern of wrong type inside CASE expression"
                    | _ => fail "Pattern of wrong type inside CASE expression"
                  end
                | (M.Valcon0pat x, Tycon y) =>
                  let val tp = lookup ctx x
                  in
                    case tp of
                      Tycon xt =>
                      if xt = y then []
                      else fail "Pattern of wrong type inside CASE expression"
                    | _ => fail "Pattern of wrong type inside CASE expression"
                  end
                | _ =>
                  fail "Pattern of wrong type inside CASE expression"

            fun synthclause [] = []
              | synthclause ((p, e) :: cs) =
                (synth (extend_list ctx (checkpat ctx p t)) e) :: (synthclause cs)

            val clausesType = synthclause cs
            val goals = C.flatten (C.expandGoal (dtctx ctx) (C.Goal t) patterns)
        in
          if List.all (fn x => Type.eq (x, hd clausesType)) clausesType then
            if C.coverageCheck patterns goals then
              hd clausesType
            else
              fail "Patterns don't cover all cases"
          else
            fail "Type of clauses don't agree"
        end

      | M.If (e, e1, e2) =>
        let val _ = check ctx e Type.Bool
            val t1 = synth ctx e1
            val t2 = synth ctx e2
        in
          if Type.eq (t1, t2) then
            t1
          else
            fail "Different types synthesized for THEN clause and ELSE clause"
        end

      | x =>
        fail ("Can't synthesize type for expression: " ^ Print.expToString x)

  (* check : context -> M.exp -> tp -> unit
   *
   * Check an expression against a type.
   * Returns () if it succeeds; otherwise raises TypeError.
   *) 
  and check ctx exp t =
      case (exp, t) of
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

                    fun build_dt ((name, ts) :: vs) =
                        C.VC (name, map (fn Int => C.BuiltIn Int
                                        | Bool => C.BuiltIn Bool
                                        | Tycon x => C.Dummy x
                                        | _ => fail "bitype.sml: 256")
                                      ts)
                        :: build_dt vs
                      | build_dt [] = []
                        
                    val tmp = bind_valcons ctx vs
                    val dt = C.DataType (t, build_dt vs)
                    val result = extend_dt tmp dt
                in
                  result
                end
      in
        bind ctx_dec rest
      end
end
