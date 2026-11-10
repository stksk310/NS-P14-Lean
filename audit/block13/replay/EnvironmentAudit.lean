module
import NSP14
import tests.ActualGradedBaseChange
import tests.BettiBaseChange
import tests.FilteredHomology
import tests.GradedKoszul
import tests.KoszulActual
import tests.KoszulComplex
import tests.KoszulExactness
import tests.KoszulFiniteModules
import tests.KoszulPresentation
import tests.KoszulTor
import tests.MinimalResolution
import tests.PolynomialBaseChange
import tests.RankEuler
import tests.Run13ClosureFixtures
import tests.Run13Fixtures
import tests.StandardMonomials
import tests.TorNaturality

import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
  let env ← getEnv
  let tests : Array String := #["tests.ActualGradedBaseChange","tests.BettiBaseChange","tests.FilteredHomology","tests.GradedKoszul","tests.KoszulActual","tests.KoszulComplex","tests.KoszulExactness","tests.KoszulFiniteModules","tests.KoszulPresentation","tests.KoszulTor","tests.MinimalResolution","tests.PolynomialBaseChange","tests.RankEuler","tests.Run13ClosureFixtures","tests.Run13Fixtures","tests.StandardMonomials","tests.TorNaturality"]
  for (n,ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!.toString
    if modName.startsWith "NSP14.Homological." || tests.contains modName then
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
      let type ← Lean.Meta.ppExpr ci.type
      let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
      IO.println ((Json.mkObj [("name",toJson n.toString),("module",toJson modName),
        ("kind",toJson kind),("axioms",toJson (axs.map Name.toString)),
        ("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]).compress)
