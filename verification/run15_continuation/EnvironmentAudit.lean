module
import NSP14
import tests.SmallScalar
import tests.Sidon
import tests.Resources
import tests.LowRank
import tests.LargeSeed
import tests.LargeScalar
import tests.OrdinaryNumerical
import tests.SemigroupFoundations
import tests.SemigroupRing
import tests.TangentAlgebra
import tests.AperyQuotient
import tests.Run12BasicExamples
import tests.Run12Fixtures
import tests.JumpBounds
import tests.PolynomialAction
import tests.JumpStrata
import tests.CompletedComparison
import tests.Run12Axioms
import tests.Run13Fixtures
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
import tests.StandardMonomials
import tests.TorNaturality
import audit.DomainChecks
import audit.block02.AssumptionChecks
import tests.Run14Fixtures
import tests.ActualSidon
import tests.OffsetStabilization
import tests.Run14Acceptance
import audit.run14.RemainingGoals
import tests.GreenLinearAlgebra
import tests.Run14Closure
import tests.Run14Volume
import audit.run14_continuation.ClosedGoals
import tests.ArithmeticSequence
import tests.ArithmeticSequenceApery
import tests.ArithmeticSequenceOrder
import tests.BettiEuler
import tests.CoefficientComparison
import tests.CutBasis
import tests.CutFinite
import tests.CutPolynomialInjection
import tests.FiniteKoszulEuler
import tests.FunctionalMinor
import tests.GradedBasis
import tests.Harmonic
import tests.IntervalCompletion
import tests.JumpEuler
import tests.KoszulSlots
import tests.LinearVariables
import tests.OrderedQuotientBasis
import tests.OrdinaryTor
import tests.RelativePresentation
import tests.Run13Axioms
import tests.Run15Actual
import tests.SemigroupAlgebraPresentation
import tests.TowerHarmonic
import audit.run15.RemainingGoals
import audit.run15_continuation.ClosedGoals
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.SmallScalar","tests.Sidon","tests.Resources","tests.LowRank","tests.LargeSeed","tests.LargeScalar","tests.OrdinaryNumerical","tests.SemigroupFoundations","tests.SemigroupRing","tests.TangentAlgebra","tests.AperyQuotient","tests.Run12BasicExamples","tests.Run12Fixtures","tests.JumpBounds","tests.PolynomialAction","tests.JumpStrata","tests.CompletedComparison","tests.Run12Axioms","tests.Run13Fixtures","tests.ActualGradedBaseChange","tests.BettiBaseChange","tests.FilteredHomology","tests.GradedKoszul","tests.KoszulActual","tests.KoszulComplex","tests.KoszulExactness","tests.KoszulFiniteModules","tests.KoszulPresentation","tests.KoszulTor","tests.MinimalResolution","tests.PolynomialBaseChange","tests.RankEuler","tests.Run13ClosureFixtures","tests.StandardMonomials","tests.TorNaturality","audit.DomainChecks","audit.block02.AssumptionChecks","tests.Run14Fixtures","tests.ActualSidon","tests.OffsetStabilization","tests.Run14Acceptance","audit.run14.RemainingGoals","tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals","tests.ArithmeticSequence","tests.ArithmeticSequenceApery","tests.ArithmeticSequenceOrder","tests.BettiEuler","tests.CoefficientComparison","tests.CutBasis","tests.CutFinite","tests.CutPolynomialInjection","tests.FiniteKoszulEuler","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.IntervalCompletion","tests.JumpEuler","tests.KoszulSlots","tests.LinearVariables","tests.OrderedQuotientBasis","tests.OrdinaryTor","tests.RelativePresentation","tests.Run13Axioms","tests.Run15Actual","tests.SemigroupAlgebraPresentation","tests.TowerHarmonic","audit.run15.RemainingGoals","audit.run15_continuation.ClosedGoals"]
 let newModules : Array String := #["NSP14.Homological.FiniteDegreeSum","NSP14.Homological.FunctionalMinor","NSP14.Homological.GeneratedDegreePresentation","NSP14.Homological.GradedBasis","NSP14.Homological.GradedMonomials","NSP14.Homological.Harmonic","NSP14.Homological.InitialModule","NSP14.Homological.KoszulArrowWedge","NSP14.Homological.KoszulChainBasis","NSP14.Homological.KoszulSlotArrow","NSP14.Homological.KoszulSlotDifferential","NSP14.Homological.KoszulSlotMaps","NSP14.Homological.KoszulSlots","NSP14.Homological.KoszulStandardMinor","NSP14.Homological.KoszulVariableSpace","NSP14.Homological.KoszulWeightedRank","NSP14.Homological.ModuleTermArithmetic","NSP14.Homological.OrderedQuotientBasis","NSP14.Homological.StandardHarmonic","NSP14.Homological.WedgeCounting","NSP14.Homological.WedgeExponent","NSP14.Homological.WeightedPivot","NSP14.Ordinary.HarmonicWeights","NSP14.Ordinary.TowerCombined","NSP14.Ordinary.TowerGrading","NSP14.Ordinary.TowerH0","NSP14.Ordinary.TowerHarmonic","NSP14.Ordinary.TowerResourceWeights","NSP14.Ordinary.TowerRow","NSP14.Ordinary.TowerTerminal","NSP14.Semigroup.TruncGradingCoordinates","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.KoszulSlots","tests.OrderedQuotientBasis","tests.TowerHarmonic","audit.run15_continuation.ClosedGoals"]
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
