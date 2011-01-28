signature COVERAGE = sig

  datatype dt = BuiltIn of Type.tp
              | DataType of vc list

       and vc = VC of MinML.name * dt list

  datatype goal = Goal of Type.tp * goalStatus * goalShape

       and goalStatus = Sat | Unsat

       and goalShape = Leaf | Branch of goal list

  val cover : goal -> MinML.pattern -> goal

end; (* signature COVERAGE *)

structure Coverage  = struct

  exception Unimplemented
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
                | SatGoal

       (* and goalStatus = Sat | Unsat *)

       and goalShape = Leaf | Branch of goal list

  type context = dt list

  val ctx = [DataType ("nat", [VC ("z", []), VC ("succ", [Dummy "nat"])])]

  exception NotFoundCoverage
  fun lookup [] _ = raise NotFoundCoverage
    | lookup (DataType (n, vcs) :: ds) x =
      if n = x then vcs else lookup ds x
    | lookup (_ :: ds) x = lookup ds x

  fun split (Goal T.Bool) = BranchGoal [TrueGoal, FalseGoal]
    | split (Goal (T.Product ts)) = TupleGoal (map (fn t => Goal t) ts)
    | split (Goal (T.Tycon t)) =
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
    | split _ = raise CoverageError "function Coverage.split: impossible"

  fun allSat gs = List.all (fn SatGoal => true | _ => false) gs

  fun cover SatGoal _ = SatGoal
    | cover (Goal _) (M.Varpat _) = SatGoal
    | cover (g as Goal T.Int) p = g (* won't split int pattern,
                                     * requires a catch-all pattern at the end
                                     *)
    | cover (g as Goal _) p = cover (split g) p
    | cover (BranchGoal gs) p =
      let val gs = map (fn g => cover g p) gs
      in
        if allSat gs then SatGoal
        else BranchGoal gs
      end
    | cover (TupleGoal gs) (M.Tuplepat ps) =
      if length gs = length ps then
        let val gs' = map (fn (g, p) => cover g p) (ListPair.zip (gs, ps))
        in
          if allSat gs' then SatGoal
          else TupleGoal gs'
        end
      else
        TupleGoal gs
    | cover (g as ValconGoal (n, gg)) (M.Valconpat (n', p)) =
      if n = n' then cover gg p
      else g
    | cover (g as Valcon0Goal n) (M.Valcon0pat n') =
      if n = n' then SatGoal else g
    | cover TrueGoal (M.Boolpat true) = SatGoal
    | cover FalseGoal (M.Boolpat false) = SatGoal
    | cover g _ = g

  fun foo x = true
end (* structure Coverage *)
