signature COVERAGE = sig

  exception CoverageError of string

end; (* signature COVERAGE *)

structure Coverage  = struct

  exception CoverageError of string

  structure M = MinML
  structure T = Type

  datatype dt = BuiltIn of Type.tp
              | DataType of (M.name * vc list)
              | Dummy of M.name

       and vc = VC of M.name * dt list

  datatype goal = Goal of Type.tp
                | BranchGoal of goal list
                | TupleGoal of goal list
                | ValconGoal of M.name * goal
                | Valcon0Goal of M.name
                | TrueGoal
                | FalseGoal

       (* and goalStatus = Sat | Unsat *)

       and goalShape = Leaf | Branch of goal list

  type context = dt list

  val ctx = [DataType ("nat", [VC ("z", []), VC ("succ", [Dummy "nat"])])]
  val ps = [M.Valconpat ("succ", M.Valconpat ("succ", M.Varpat "x")),
            M.Valcon0pat "z"]
  val ps2 = [M.Valconpat ("succ", M.Valconpat ("succ", M.Varpat "x")),
             M.Valconpat ("succ", M.Varpat "x"),
             M.Valcon0pat "z"]

  exception NotFoundCoverage
  fun lookup [] _ = raise NotFoundCoverage
    | lookup (DataType (n, vcs) :: ds) x =
      if n = x then vcs else lookup ds x
    | lookup (_ :: ds) x = lookup ds x

  fun split ctx (Goal T.Bool) = BranchGoal [TrueGoal, FalseGoal]
    | split ctx (Goal (T.Product ts)) = TupleGoal (map (fn t => Goal t) ts)
    | split ctx (Goal (T.Tycon t)) =
      let val vcs = lookup ctx t

          fun dt2goal (BuiltIn t) = Goal t
            | dt2goal (Dummy t) = Goal (T.Tycon t)
            | dt2goal _ = raise CoverageError "coverage.sml: 62"

          fun vc2goal (VC (n, dts)) =
              case dts of
                [] =>  Valcon0Goal n
              | [dt] => ValconGoal (n, dt2goal dt)
              | dts => ValconGoal (n, TupleGoal (map dt2goal dts))

          val gs = map vc2goal vcs
      in
        BranchGoal gs
      end
    | split _ _ = raise CoverageError "function Coverage.split: impossible"

  (* expand : goal -> MinML.pattern -> goal
   * Given a goal and a pattern, furthur split the goal as needed
   *)
  fun expand ctx (g as Goal _) (M.Varpat _) = g
    | expand ctx (g as Goal _) p = expand ctx (split ctx g) p
    | expand ctx (BranchGoal gs) p = BranchGoal (map (fn g => expand ctx g p) gs)
    | expand ctx (TupleGoal gs) (M.Tuplepat ps) =
      if length gs = length ps then
        TupleGoal (map (fn (g, p) => expand ctx g p) (ListPair.zip (gs, ps)))
      else
        raise CoverageError "coverage.sml 82: impossible"
    | expand ctx (g as ValconGoal (n, gg)) (M.Valconpat (n', p)) =
      if n = n' then ValconGoal (n, expand ctx gg p)
      else g
    | expand _ g _ = g

  fun expandGoal ctx g [] = g
    | expandGoal ctx g (p :: ps) = expandGoal ctx (expand ctx g p) ps

  (* flatten : goal -> goal list
   * eliminate BranchGoal to produce a list of coverage goals
   *)
  fun flatten (BranchGoal gs) = foldl (op @) [] (map flatten gs)
    | flatten (TupleGoal []) = [TupleGoal []]
    | flatten (TupleGoal (g1 :: gs)) =
      let val g1s = flatten g1
          val rest = flatten (TupleGoal gs)
      in
        foldl (op @) [] (map (fn g => map (fn TupleGoal gs' => TupleGoal (g :: gs')
                                            | _ => raise CoverageError "coverage.sml: 97")
                                          rest)
                             g1s)
      end
    | flatten (ValconGoal (n, g)) = map (fn g => ValconGoal (n, g)) (flatten g)
    | flatten g = [g]

  (* cover : MinML.pattern -> goal -> bool
   * Given a pattern and a goal (with out branches), return true iff the pattern covers
   * the goal
   *)
  fun cover (M.Varpat _) _ = true
    | cover (M.Boolpat true) TrueGoal = true
    | cover (M.Boolpat false) FalseGoal = true
    | cover (M.Tuplepat ps) (TupleGoal gs) =
      List.all (fn (p, g) => cover p g) (ListPair.zip (ps, gs))
    | cover (M.Valconpat (n, p)) (ValconGoal (n', g)) = (n = n' andalso cover p g)
    | cover (M.Valcon0pat n) (Valcon0Goal n') = n = n'
    | cover _ _ = false

  fun coverageCheck _ [] = true
    | coverageCheck [] _ = false
    | coverageCheck (p :: ps) gs = coverageCheck ps
                                                 (List.filter (not o (cover p)) gs)

  fun coverageCheckProgram ctx exp =
      let val cc = coverageCheckProgram ctx
      in
        case exp of
          M.If (e, e1, e2) => (cc e; cc e1; cc e2)
        | M.Tuple es => (map cc es; ())
        | M.Fn (_, body) => cc body
        | M.Rec (_, _, body) => cc body
        | M.Apply (e1, e2) => (cc e1; cc e2)
        | M.Anno (e, _) => cc e
        | M.Valcon (_, e) => cc e
        | M.Primop (p, es) => (map cc es; ())
        | e => ()
      end

end (* structure Coverage *)

(*
val gt2 = expandGoal (Goal (Type.Tycon "nat")) ps2;
val gs2 = flatten gt2;
val res = coverageCheck ps2 gs2;
*)
