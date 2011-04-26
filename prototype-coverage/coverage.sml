signature COVERAGE = sig

  exception CoverageError of string

  datatype dt = BuiltIn of Type.tp
              | DataType of (MinML.name * vc list)
              | Dummy of MinML.name

       and vc = VC of MinML.name * dt list

  datatype goal = Goal of Type.tp
                | BranchGoal of goal list
                | TupleGoal of goal list
                | ValconGoal of MinML.name * goal
                | Valcon0Goal of MinML.name
                | TrueGoal
                | FalseGoal

  type context = dt list

  val expandGoal : context -> goal -> MinML.pattern list -> goal
  val flatten : goal -> goal list
  val coverageCheck : MinML.pattern list -> goal list -> bool

end; (* signature COVERAGE *)

structure Coverage :> COVERAGE = struct

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

  type context = dt list

  val ctx = [DataType ("nat", [VC ("z", []), VC ("succ", [Dummy "nat"])])]
  val ps = [M.Valconpat ("succ", M.Valconpat ("succ", M.Varpat "x")),
            M.Valcon0pat "z"]
  val ps2 = [M.Valconpat ("succ", M.Valconpat ("succ", M.Varpat "x")),
             M.Valconpat ("succ", M.Varpat "x"),
             M.Valcon0pat "z"]

  exception NotFoundCoverage
  fun lookup [] _ = raise CoverageError "Datatype not found in environment"
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
    | split _ _ = raise CoverageError "coverage.sml: 82"

  (* expand : context -> goal -> MinML.pattern -> goal
   * Given a contex, a goal and a pattern, furthur split the goal as needed
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

  (* expandGoal : contex -> goal -> pattern list -> goal
   *)
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

  (* coverageCheck : pattern list -> goal list -> bool
   * Given a list of patterns and a list of goals, check if the patterns covers
   * all the goals
   *)
  fun coverageCheck _ [] = true
    | coverageCheck [] _ = false
    | coverageCheck (p :: ps) gs = coverageCheck ps
                                                 (List.filter (not o (cover p)) gs)

end (* structure Coverage *)

(*
val gt2 = expandGoal (Goal (Type.Tycon "nat")) ps2;
val gs2 = flatten gt2;
val res = coverageCheck ps2 gs2;
*)
