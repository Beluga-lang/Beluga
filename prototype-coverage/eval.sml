(* TODO:
 * - in function `subst': rename variables in the clauses of
 *   CASE expression to avoid capturing of the free variables in
 *   the expression being substituted in.
 *)

(* Evaluation of MinML expressions via big step semantics *)
signature EVAL = sig

  exception Stuck of string

  val subst : MinML.exp * MinML.name -> MinML.exp -> MinML.exp

  (* big-step evaluation; raises Stuck if evaluation is not possible *)
  val eval : MinML.exp -> MinML.exp

  (* 0 for no debugging printing, 1 for printing in eval, 2 for eval and subst *)
  val verbose : int ref

end;  (* signature EVAL *)

structure Eval :> EVAL = struct

  val verbose = ref 0
  val bigstep_depth = ref 0
  fun indent 0 = ""
    | indent n = " " ^ indent (n - 1)

  structure M = MinML
  structure T = Type

  exception Stuck of string
  exception Unimplemented

  local
    (* to generate new internal variables *)
    val counter = ref 0
  in
    (* freshVar x = a, where a is a new internal variable.
     * Internal variables begin with a natural number,
     * so they cannot conflict with external variables.
     *)
    fun freshVar x =
        (counter := !counter+1;
         Int.toString (!counter) ^ x)

    fun resetCtr () = 
        counter := 0
  end

  (* ------------------------------------------------------------
   * Free variables
   * ------------------------------------------------------------ *)

  fun member x l = List.exists (fn y => y = x) l

  fun union ([], l) = l
    | union (x :: t, l) = 
      if member x l then union (t,l)
      else x :: union (t,l)

  fun unionList sets = foldr (fn (s1, s2) => union(s1, s2)) [] sets

  fun delete (vlist,[]) = []
    | delete (vlist, h :: t) = 
      if member h vlist then delete (vlist,t)
      else h :: delete (vlist,t)

  fun boundVars dec = case dec of
                        M.Val (_, name) => [name]
                      | M.Valtuple(_, names) => names
                      | M.Datatype _ => []

  fun boundVarsPattern (M.Varpat x) = [x]
    | boundVarsPattern (M.Tuplepat ps) = unionList (map boundVarsPattern ps)
    | boundVarsPattern (M.Valconpat (_, p)) = boundVarsPattern p
    | boundVarsPattern _ = []

  fun varsDecs [] = ([], [])
    | varsDecs (dec1::decs) =
      let
        val (free, bound) = varsDecs decs
      in
        (union (freeVarsDec dec1, delete (boundVars dec1, free)), bound)
      end

  and freeVarsDec dec = case dec of
                          M.Val (exp, name) => freeVars exp
                        | M.Valtuple (exp, names) => freeVars exp
                        | M.Datatype _ => []

  (* freeVars(e) = list of names occurring free in e 
   *
   * Invariant: every name occurs at most once.
   *)
  and freeVars exp = case exp of
                       M.Var y => [y]
                     | M.Int n => []
                     | M.Bool b => []
                     | M.If (e, e1, e2) =>
                       union (freeVars e, 
                              union(freeVars e1, freeVars e2))
                     | M.Primop (po, args) =>
                       foldr (fn (e1,e2) => union(freeVars e1, e2)) [] args 
                     | M.Tuple exps =>
                       unionList (List.map freeVars exps)
                     | M.Fn(x, e) =>
                       delete([x], freeVars e)
                     | M.Rec(x, t, e) =>
                       delete([x], freeVars e)
                     | M.Let(decs, e2) =>
                       let
                         val (free, bound) = varsDecs decs
                       in
                         union(free, delete(bound, freeVars e2))
                       end
                     | M.Apply(e1, e2) =>
                       union(freeVars e1, freeVars e2)
                     | M.Anno(e, _) =>
                       freeVars e
                     | M.Case (e, cs) =>
                       let val bsfs = map (fn (p, e') => ((boundVarsPattern p), (freeVars e')))
                                        cs
                           val fs = map delete bsfs
                       in
                         union (freeVars e, unionList fs)
                       end
                     | M.Valcon (x, e) => freeVars e
                     | M.Valcon0 _ => []
                     (* | M.Valcon (x, e) => union ([x], freeVars e) *)
                     (* | M.Valcon0 x => [x] *)

  (* Substitution 
   *
   * subst (e',x) e = [e/x]e 
   *
   * subst replaces every occurrence of the variable x 
   * in the expression e' with e.
   *
   * subst: (exp * string) -> exp -> exp
   *)

  fun substArg s ([]) = []
    | substArg s (a::args) = (subst s a)::(substArg s args)
                             
  and subst (s as (e',x)) exp = let
    val result = 
        case exp of
          M.Var y => if x = y then e'
                     else M.Var y

        | M.Int n => M.Int n
        | M.Bool b => M.Bool b
        | M.Primop(po, args) => M.Primop(po, substArg s args)
        | M.If(e, e1, e2) =>
          M.If(subst s e, subst s e1, subst s e2)

        | M.Tuple es =>
          M.Tuple (List.map (subst s) es)

        | M.Anno (e, t) =>
          M.Anno (subst s e, t)

        | M.Let ([], e2) => M.Let ([], subst s e2)

        | M.Let(dec1::decs, e2) =>
          let val rest = M.Let(decs, e2)
          in 
            case dec1 of
              M.Val (exp, name) =>
              let val (name, rest) =
                      if member name (freeVars e') then
                        rename (name, rest)
                      else (name, rest)
                  val exp = subst s exp
              in
                if name = x then
                  M.Let (M.Val(exp, name) :: decs, e2)
                else
                  let val M.Let (decs, e2) = subst s rest
                  in
                    M.Let (M.Val(exp, name) :: decs, e2)
                  end
              end

            | M.Valtuple(exp, names) =>
              let val (names', rest) = renameListAsNeeded names e' rest
                  val exp = subst s exp
              in
                if member x names then
                  M.Let(M.Valtuple(exp, names) :: decs, e2)
                else
                  let val M.Let(decs, e2) = subst s rest
                  in
                    M.Let(M.Valtuple(exp, names') :: decs, e2)
                  end
              end

            | e as M.Datatype _ =>
              let val M.Let (decs, e2) = subst s rest
              in
                M.Let (e :: decs, e2)
              end
          end

        | M.Apply (e1, e2) => M.Apply (subst s e1, subst s e2)

        | M.Fn (y, e) =>
          if y = x then
            M.Fn (y, e)
          else
            if member y (freeVars e') then
              let val (y,e1) = rename (y,e)
              in
                M.Fn (y, subst s e1)
              end
            else
              M.Fn(y, subst s e)

        | M.Rec (y, t, e) =>
          if y = x then
            M.Rec (y, t, e)
          else
            if member y (freeVars e') then
              let val (y, e1) = rename (y, e)
              in
                M.Rec (y, t, subst s e1)
              end
            else
              M.Rec (y, t, subst s e)

        | M.Case (e, cs) =>
          let fun substClauses _ [] = []
                | substClauses (s as (e', x)) ((p, e) :: cs) =
                  let val bound = boundVarsPattern p
                  in
                    if member x bound then
                      (p, e) :: substClauses s cs
                    else
                      (p, subst s e) :: substClauses s cs
                  end
          in
            M.Case (subst s e, substClauses s cs)
          end
        | M.Valcon (n, e) => M.Valcon (n, subst s e)
        | e as M.Valcon0 _ => e
  in
    if !verbose >= 2 then
      print ("subst: " ^ Print.expToString e' ^ " for " ^ x ^ " in " ^
             Print.expToString exp ^ "\n =    " ^ Print.expToString result ^ "\n")
    else ();
    result
  end  

  and substList [] e = e
    | substList ((x,e')::pairs) e =
      subst (x,e') (substList pairs e)

  and substType (s as (e',x)) t =
      let val result = 
              case t of
                T.Arrow (t1, t2) => T.Arrow (substType s t1, substType s t2)
              | T.Product ts => T.Product (List.map (substType s) ts)
              | T.Int => T.Int
              | T.Bool => T.Bool
              | T.Awesome => T.Awesome
              | T.Tycon x => T.Tycon x
      in
        if !verbose >= 2 then
          print ("substType: " ^ Print.expToString e' ^ " for " ^ x ^ " in "
                 ^ Print.typeToString t ^ "\n =    " ^ Print.typeToString result ^ "\n")
        else () ;
        result
      end  

  and rename (x, e) = 
      let
        val x' = freshVar x
      in
        (x', subst (M.Var x', x) e)
      end

  and rename2 (x, y, e1, e2) = 
      let
        val x' = freshVar x 
        val y' = freshVar y 
        fun subst2 e = subst (M.Var x', x) (subst (M.Var y', y) e)
      in
        (x', y', subst2 e1, subst2 e2)
      end

  and renameAll ([], e) = ([], e)
    | renameAll (x::xs, e) = 
      let
        val (x', e) = rename (x, e)
        val (xs', e) = renameAll (xs, e)
      in
        (x' :: xs', e)
      end

  and renameListAsNeeded names e' exp =
      if List.exists (fn name => member name (freeVars e')) names then
        renameAll(names, exp)
      else
        (names, exp)


  (*------------------------------------------------------------------
   * Big-step evaluation
   *-------------------------------------------------------------------*)

  fun evalList (exps : M.exp list) =
      List.map eval exps

  and evalValtuple (e1, xs, decs, e2) =
      case eval e1 of
        M.Tuple es =>
        if length es = length xs then
          eval (substList (ListPair.zip (es, xs)) (M.Let(decs, e2)))
        else
          raise Stuck "Tuple binding failure (length mismatch)"

      | _ => raise Stuck "Tuple binding failure"

  and evalDatatype (cs, decs, e2) =
      let fun foo ([], e2) = eval e2
            | foo ((valcon, []) :: cs, e2) =
              foo (cs, (subst ((M.Valcon0 valcon), valcon) e2))
            | foo ((valcon, _) :: cs, e2) =
              let val arg = freshVar "valcon_arg"
              in
                foo (cs, (subst ((M.Fn (arg, M.Valcon (valcon, M.Var arg))), valcon) e2))
              end
      in
        foo (cs, e2)
      end


  (* eval : exp -> exp *)
  and eval exp = let
    val _ = if !verbose >= 1 then
              print (indent (!bigstep_depth) ^ "eval { " ^ Print.expToString exp ^ " }\n")
            else ()
    val _ = bigstep_depth := !bigstep_depth + 1
    val result = 
        case exp of
          (* Values evaluate to themselves... *)
          e as M.Fn _ => e
        | e as M.Int _ => e
        | e as M.Bool _ => e
        | e as M.Valcon0 _ => e
        | e as M.Valcon _ => e

        | M.Var x => raise Stuck ("Free variable (" ^ x ^ ") during evaluation")

        | recursiveExp as M.Rec (f, t, e) =>
          eval (M.Anno (subst (recursiveExp, f) e, t))
          
        (* primitive operations +, -, *, <, = *)
        | M.Primop(po, args) =>
          let val argvalues = evalList args
          in case M.evalOp(po, argvalues) of
               NONE => raise Stuck "Bad arguments to primitive operation"
             | SOME v => v
          end

        | M.Tuple es => M.Tuple (evalList es)

        | M.Let([], e2) => eval e2
        | l as M.Let(dec1::decs, e2) => 
          let in
            case dec1 of
              M.Val(e1, x) =>
              (* call-by-value *)
              let val v1 = eval e1
              in
                eval (subst (v1, x) (M.Let(decs, e2)))
              end
            | M.Valtuple(e1, xs) => evalValtuple (e1, xs, decs, e2)
            | M.Datatype (x, cs) => evalDatatype (cs, decs, (M.Let (decs, e2)))

          end

        | M.Anno (e, t) => eval e

        | M.If(e, e1, e2) =>
          let in
            case eval e of
              M.Bool true => eval e1
            | M.Bool false => eval e2
            | _ => raise Stuck "Condition of if-expression not Boolean"
          end

        | M.Apply (e1, e2) =>
          let in
            case eval e1 of
              M.Fn (x, body) =>
              let val v2 = eval e2
                  val body = subst (v2, x) body
              in
                eval body
              end
            | _ => raise Stuck "Apply: e1 evaluated to non-function"
          end

        | M.Case (e, cs) =>
          let exception MatchError
              fun match e p =
                  case (e, p) of
                    (e, M.Varpat x) => [(e, x)]
                  | (M.Int i, M.Intpat j) =>
                    if i = j then [] else raise MatchError
                  | (M.Bool b, M.Boolpat c) =>
                    if b = c then [] else raise MatchError
                  | (M.Tuple es, M.Tuplepat ps) =>
                    if length es = length ps then
                      foldl (op @)
                            []
                            (map (fn (e, p) => match e p)
                                 (ListPair.zip (es, ps)))
                    else
                      raise MatchError
                  | (M.Valcon (x, e'), M.Valconpat (y, p')) =>
                    if x = y then match e' p' else raise MatchError
                  | (M.Valcon0 x, M.Valcon0pat y) =>
                    if x = y then [] else raise MatchError
                  | _ => raise MatchError

              fun patternMatch _ [] =
                  raise Stuck "Case: non-exhausitve pattern matching"
                | patternMatch e ((p, body) :: rest) =
                  ((match e p), body)
                  handle MatchError => patternMatch e rest

              val (bindings, body) = patternMatch (eval e) cs
          in
            eval (substList bindings body)
          end
  in
    bigstep_depth := !bigstep_depth - 1;
    if !verbose >= 1 then
      print (indent (!bigstep_depth)
             ^ "result of eval { " ^ Print.expToString exp ^ " } = "
             ^ Print.expToString result ^ "\n")
    else ();
    result
  end

end  (* structure Eval *)
