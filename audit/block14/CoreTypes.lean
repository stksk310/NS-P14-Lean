module
import NSP14
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["NSP14.Combinatorics.FiniteRank","NSP14.Green.BilinearQuotient","NSP14.Green.BilinearSpan","NSP14.Green.CutImage","NSP14.Green.ExtendIndependent","NSP14.Green.FlagSpan","NSP14.Green.FormProducts","NSP14.Green.HyperplaneFlag","NSP14.Green.HyperplaneStep","NSP14.Green.MaximalRank","NSP14.Green.Perturbation","NSP14.Green.QuadraticRank","NSP14.Green.RankChoice","NSP14.Homological.InfiniteScalarField","NSP14.Ordinary.ActualWitness","NSP14.Ordinary.OffsetVolumeArithmetic","NSP14.Ordinary.QuadraticCutRank","NSP14.Semigroup.ActualCutRank","NSP14.Semigroup.ActualFinite","NSP14.Semigroup.ActualGreen","NSP14.Semigroup.ActualLayers","NSP14.Semigroup.ActualResources","NSP14.Semigroup.ActualSidon","NSP14.Semigroup.CutAction","NSP14.Semigroup.CutAugmentation","NSP14.Semigroup.CutGeneration","NSP14.Semigroup.CutGeneratorCount","NSP14.Semigroup.FixedTower","NSP14.Semigroup.HeadResource","NSP14.Semigroup.HighIdeal","NSP14.Semigroup.IntervalCap","NSP14.Semigroup.IntervalMass","NSP14.Semigroup.LinearForms","NSP14.Semigroup.OffsetLevel","NSP14.Semigroup.OffsetPaths","NSP14.Semigroup.OffsetStabilization","NSP14.Semigroup.OffsetTelescoping","NSP14.Semigroup.OffsetVolume","NSP14.Semigroup.QuadraticProduct","NSP14.Semigroup.SquareZeroCut","NSP14.Semigroup.TerminalResidues","NSP14.Semigroup.TowerCoordinates","NSP14.Semigroup.TowerExact","NSP14.Semigroup.TowerIdeals","NSP14.Semigroup.TowerIntervals","NSP14.Semigroup.TowerResources","NSP14.Semigroup.TowerStratum","NSP14.Semigroup.TruncCoordinates","NSP14.Semigroup.TruncGeneration"]
 for (n, ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if included.contains modName then
   let axs ← collectAxioms n
   let tp ← Meta.ppExpr ci.type
   let ep ← withOptions (fun o => o.setBool `pp.explicit true) (Meta.ppExpr ci.type)
   IO.println ((Json.mkObj [("name", toJson n.toString), ("module", toJson modName),
     ("type", toJson tp.pretty), ("explicit_type", toJson ep.pretty),
     ("axioms", toJson (axs.map Name.toString))]).compress)
