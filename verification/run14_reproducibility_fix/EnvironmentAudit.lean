module
import NSP14
import tests.GreenLinearAlgebra
import tests.Run14Closure
import tests.Run14Volume
import audit.run14_continuation.ClosedGoals
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals"]
 let newModules : Array String := #["NSP14.Combinatorics.FiniteRank","NSP14.Green.BilinearQuotient","NSP14.Green.BilinearSpan","NSP14.Green.CutImage","NSP14.Green.ExtendIndependent","NSP14.Green.FlagSpan","NSP14.Green.FormProducts","NSP14.Green.HyperplaneFlag","NSP14.Green.HyperplaneStep","NSP14.Green.MaximalRank","NSP14.Green.Perturbation","NSP14.Green.QuadraticRank","NSP14.Green.RankChoice","NSP14.Ordinary.ActualWitness","NSP14.Ordinary.OffsetVolumeArithmetic","NSP14.Semigroup.ActualGreen","NSP14.Semigroup.ActualResources","NSP14.Semigroup.CutAction","NSP14.Semigroup.CutAugmentation","NSP14.Semigroup.CutGeneration","NSP14.Semigroup.CutGeneratorCount","NSP14.Semigroup.FixedTower","NSP14.Semigroup.HeadResource","NSP14.Semigroup.HighIdeal","NSP14.Semigroup.IntervalCap","NSP14.Semigroup.IntervalMass","NSP14.Semigroup.LinearForms","NSP14.Semigroup.OffsetLevel","NSP14.Semigroup.OffsetVolume","NSP14.Semigroup.QuadraticProduct","NSP14.Semigroup.SquareZeroCut","NSP14.Semigroup.TerminalResidues","NSP14.Semigroup.TowerCoordinates","NSP14.Semigroup.TowerExact","NSP14.Semigroup.TowerIntervals","NSP14.Semigroup.TowerStratum","NSP14.Semigroup.TruncCoordinates","NSP14.Semigroup.TruncGeneration","tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals"]
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if modName == "NSP14" || modName.startsWith "NSP14." || included.contains modName then
   let axs ← collectAxioms n
   let kind := match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
   let mut fields := [("name",toJson n.toString),("module",toJson modName),
    ("exported_kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if newModules.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
