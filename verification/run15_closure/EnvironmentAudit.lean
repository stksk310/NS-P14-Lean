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
import tests.ArithmeticSequenceMaximalBetti
import tests.ArithmeticSequenceConeBetti
import tests.APKernelWindow
import tests.APLowerRows
import tests.APResolutionFoundations
import tests.ActualTorRow
import tests.ArithmeticSequence
import tests.ArithmeticSequenceApery
import tests.ArithmeticSequenceBetti
import tests.ArithmeticSequenceKernelTor
import tests.ArithmeticSequenceOrder
import tests.BettiEuler
import tests.ChangingOrdinaryClosure
import tests.CoefficientComparison
import tests.CutBasis
import tests.CutFinite
import tests.CutPolynomialInjection
import tests.TowerHarmonic
import tests.CutResidual
import tests.FiniteKoszulEuler
import tests.FunctionalMinor
import tests.GradedBasis
import tests.Harmonic
import tests.HeadFirstOrder
import tests.IntervalAPBetti
import tests.IntervalCompletion
import tests.IntrinsicFullTransfer
import tests.JumpEuler
import tests.KoszulSlots
import tests.LinearVariableBetti
import tests.LinearVariables
import tests.NativeCutH0
import tests.OrderedQuotientBasis
import tests.OrdinaryClosure
import tests.OrdinaryTor
import tests.RelativePresentation
import tests.RelativeXComparison
import tests.Run13Axioms
import tests.Run15Actual
import tests.SemigroupAlgebraPresentation
import tests.SquareZeroEuler
import tests.TwoStepActual
import audit.run15.RemainingGoals
import audit.run15_continuation.ClosedGoals
import audit.run15_xclosure.ClosedGoals
import audit.run15_bclosure.ClosedGoals
import audit.run15_h0closure.ClosedGoals
import audit.run15_fulltransfer.ClosedGoals
import audit.run15_ordinary.ClosedGoals
import audit.run15_apcone.ClosedGoals
import audit.run15_apfoundations.Scope
import audit.run15_closure.ClosedGoals
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.SmallScalar","tests.Sidon","tests.Resources","tests.LowRank","tests.LargeSeed","tests.LargeScalar","tests.OrdinaryNumerical","tests.SemigroupFoundations","tests.SemigroupRing","tests.TangentAlgebra","tests.AperyQuotient","tests.Run12BasicExamples","tests.Run12Fixtures","tests.JumpBounds","tests.PolynomialAction","tests.JumpStrata","tests.CompletedComparison","tests.Run12Axioms","tests.Run13Fixtures","tests.ActualGradedBaseChange","tests.BettiBaseChange","tests.FilteredHomology","tests.GradedKoszul","tests.KoszulActual","tests.KoszulComplex","tests.KoszulExactness","tests.KoszulFiniteModules","tests.KoszulPresentation","tests.KoszulTor","tests.MinimalResolution","tests.PolynomialBaseChange","tests.RankEuler","tests.Run13ClosureFixtures","tests.StandardMonomials","tests.TorNaturality","audit.DomainChecks","audit.block02.AssumptionChecks","tests.Run14Fixtures","tests.ActualSidon","tests.OffsetStabilization","tests.Run14Acceptance","audit.run14.RemainingGoals","tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals","tests.ArithmeticSequenceMaximalBetti","tests.ArithmeticSequenceConeBetti","tests.APKernelWindow","tests.APLowerRows","tests.APResolutionFoundations","tests.ActualTorRow","tests.ArithmeticSequence","tests.ArithmeticSequenceApery","tests.ArithmeticSequenceBetti","tests.ArithmeticSequenceKernelTor","tests.ArithmeticSequenceOrder","tests.BettiEuler","tests.ChangingOrdinaryClosure","tests.CoefficientComparison","tests.CutBasis","tests.CutFinite","tests.CutPolynomialInjection","tests.TowerHarmonic","tests.CutResidual","tests.FiniteKoszulEuler","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.HeadFirstOrder","tests.IntervalAPBetti","tests.IntervalCompletion","tests.IntrinsicFullTransfer","tests.JumpEuler","tests.KoszulSlots","tests.LinearVariableBetti","tests.LinearVariables","tests.NativeCutH0","tests.OrderedQuotientBasis","tests.OrdinaryClosure","tests.OrdinaryTor","tests.RelativePresentation","tests.RelativeXComparison","tests.Run13Axioms","tests.Run15Actual","tests.SemigroupAlgebraPresentation","tests.SquareZeroEuler","tests.TwoStepActual","audit.run15.RemainingGoals","audit.run15_continuation.ClosedGoals","audit.run15_xclosure.ClosedGoals","audit.run15_bclosure.ClosedGoals","audit.run15_h0closure.ClosedGoals","audit.run15_fulltransfer.ClosedGoals","audit.run15_ordinary.ClosedGoals","audit.run15_apcone.ClosedGoals","audit.run15_apfoundations.Scope","audit.run15_closure.ClosedGoals"]
 let newModules : Array String := #["NSP14.ArithmeticSequence.Apery","NSP14.ArithmeticSequence.AtomIndices","NSP14.ArithmeticSequence.BettiFormula","NSP14.ArithmeticSequence.ConeBetti","NSP14.ArithmeticSequence.ConeRegular","NSP14.ArithmeticSequence.HeadIndex","NSP14.ArithmeticSequence.HeadMultiplication","NSP14.ArithmeticSequence.HeadQuotientMap","NSP14.ArithmeticSequence.Interval","NSP14.ArithmeticSequence.MaximalEmbeddingBetti","NSP14.ArithmeticSequence.ModelCoordinates","NSP14.ArithmeticSequence.ModelExactSequence","NSP14.ArithmeticSequence.ModelHeadBetti","NSP14.ArithmeticSequence.ModelKernel","NSP14.ArithmeticSequence.ModelKernelBetti","NSP14.ArithmeticSequence.ModelKernelDivision","NSP14.ArithmeticSequence.ModelKernelShift","NSP14.ArithmeticSequence.ModelMultiplication","NSP14.ArithmeticSequence.ModelNativeReduction","NSP14.ArithmeticSequence.ModelNativeWindow","NSP14.ArithmeticSequence.ModelPolynomialBetti","NSP14.ArithmeticSequence.ModelQuotient","NSP14.ArithmeticSequence.ModelTorClosure","NSP14.ArithmeticSequence.ModelVariableOrder","NSP14.ArithmeticSequence.ModelWindowAction","NSP14.ArithmeticSequence.Order","NSP14.ArithmeticSequence.OrdinaryModel","NSP14.ArithmeticSequence.ProfileBounds","NSP14.ArithmeticSequence.Source","NSP14.ArithmeticSequence.TwoGeneratorBetti","NSP14.ArithmeticSequence.Width","NSP14.ArithmeticSequence.WindowArithmetic","NSP14.ArithmeticSequence.WindowBetti","NSP14.ArithmeticSequence.WindowHankel","NSP14.ArithmeticSequence.WindowPolynomialModule","NSP14.Homological.ActionAppend","NSP14.Homological.ActionCoefficient","NSP14.Homological.ActionComplexBound","NSP14.Homological.ActionH0Ideal","NSP14.Homological.ActionH0Image","NSP14.Homological.ActionKoszul","NSP14.Homological.ActionKoszulH0","NSP14.Homological.ActionOnComplex","NSP14.Homological.ActionSingleCoefficient","NSP14.Homological.AcyclicQuotient","NSP14.Homological.ArrowCone","NSP14.Homological.BasisShiftWindow","NSP14.Homological.BettiEuler","NSP14.Homological.CoefficientConeBetti","NSP14.Homological.CoefficientFactorCone","NSP14.Homological.CoefficientKoszulCons","NSP14.Homological.CoefficientKoszulFunctor","NSP14.Homological.CoefficientKoszulListFunctor","NSP14.Homological.CoefficientKoszulSupport","NSP14.Homological.CoefficientSlotsEquiv","NSP14.Homological.ComplexEuler","NSP14.Homological.ConeDiagram","NSP14.Homological.ConeSuspension","NSP14.Homological.CorrectedActionComparison","NSP14.Homological.EndomorphismConeBound","NSP14.Homological.EvaluationVariables","NSP14.Homological.ExtendPrefix","NSP14.Homological.FactorConeTerminal","NSP14.Homological.FactorRange","NSP14.Homological.FiniteDegreeSum","NSP14.Homological.FiniteKoszulEuler","NSP14.Homological.FiniteKoszulEulerAbove","NSP14.Homological.FirstOrderAction","NSP14.Homological.FirstOrderBetti","NSP14.Homological.FirstOrderResidual","NSP14.Homological.FullListBetti","NSP14.Homological.FunctionalMinor","NSP14.Homological.GeneratedDegreePresentation","NSP14.Homological.GradedBasis","NSP14.Homological.GradedMonomials","NSP14.Homological.H0KernelHomology","NSP14.Homological.H0Truncation","NSP14.Homological.HankelAction","NSP14.Homological.HankelDelta","NSP14.Homological.HankelEvaluation","NSP14.Homological.HankelModuleBetti","NSP14.Homological.Harmonic","NSP14.Homological.InitialModule","NSP14.Homological.InjectiveFactor","NSP14.Homological.KoszulArrowWedge","NSP14.Homological.KoszulChainBasis","NSP14.Homological.KoszulCoefficientSlots","NSP14.Homological.KoszulIncidence","NSP14.Homological.KoszulIndependentImages","NSP14.Homological.KoszulLinearity","NSP14.Homological.KoszulListResolution","NSP14.Homological.KoszulMomentRank","NSP14.Homological.KoszulRankOneAction","NSP14.Homological.KoszulSlotArrow","NSP14.Homological.KoszulSlotComplete","NSP14.Homological.KoszulSlotDelete","NSP14.Homological.KoszulSlotDifferential","NSP14.Homological.KoszulSlotMaps","NSP14.Homological.KoszulSlots","NSP14.Homological.KoszulStandardMinor","NSP14.Homological.KoszulVariableMaps","NSP14.Homological.KoszulVariableSpace","NSP14.Homological.KoszulWeightedRank","NSP14.Homological.LinearCoefficientAction","NSP14.Homological.LinearVariableBetti","NSP14.Homological.LinearVariables","NSP14.Homological.ModuleTermArithmetic","NSP14.Homological.MonicCone","NSP14.Homological.NativeCoefficientComplex","NSP14.Homological.NativeKoszulExact","NSP14.Homological.OptionPolynomialEquiv","NSP14.Homological.OptionVariableOrder","NSP14.Homological.OrderedQuotientBasis","NSP14.Homological.PascalBound","NSP14.Homological.PolynomialAugmentation","NSP14.Homological.PolynomialEquivBetti","NSP14.Homological.PolynomialInjection","NSP14.Homological.PolynomialRestrictionKoszul","NSP14.Homological.PositiveBinomial","NSP14.Homological.QuotientBettiAdditivity","NSP14.Homological.RankOneIncidence","NSP14.Homological.RegularActionCoefficient","NSP14.Homological.RegularAugmentationBetti","NSP14.Homological.RegularCorrectedComparison","NSP14.Homological.RegularElementQuotient","NSP14.Homological.RegularH0Dimension","NSP14.Homological.RegularModuleReduction","NSP14.Homological.RegularPolynomialReduction","NSP14.Homological.RegularRestriction","NSP14.Homological.RestrictedScalars","NSP14.Homological.ReverseWindowSplit","NSP14.Homological.RingEquivTensor","NSP14.Homological.RingEquivTor","NSP14.Homological.SquareZeroBetti","NSP14.Homological.SquareZeroEuler","NSP14.Homological.SquareZeroModel","NSP14.Homological.StandardHarmonic","NSP14.Homological.TrivSqZeroCoordinates","NSP14.Homological.TwoStepBetti","NSP14.Homological.TwoStepBoundary","NSP14.Homological.TwoStepCone","NSP14.Homological.TwoStepSlots","NSP14.Homological.VandermondeSpark","NSP14.Homological.WedgeCounting","NSP14.Homological.WedgeExponent","NSP14.Homological.WeightedPivot","NSP14.Homological.ZeroCone","NSP14.Homological.ZerothBettiEpi","NSP14.Ordinary.ActualTorRow","NSP14.Ordinary.Closure","NSP14.Ordinary.CutAlgebraRestriction","NSP14.Ordinary.CutBEuler","NSP14.Ordinary.CutBFullAction","NSP14.Ordinary.CutBModel","NSP14.Ordinary.CutFinite","NSP14.Ordinary.CutFirstOrder","NSP14.Ordinary.CutHighTwo","NSP14.Ordinary.CutResidualAction","NSP14.Ordinary.CutResidualAlgebra","NSP14.Ordinary.CutResidualModule","NSP14.Ordinary.CutXComparison","NSP14.Ordinary.CutXSequences","NSP14.Ordinary.FullVariableBetti","NSP14.Ordinary.FullVariableChange","NSP14.Ordinary.FullVariableOrder","NSP14.Ordinary.HarmonicWeights","NSP14.Ordinary.IntrinsicFullTransfer","NSP14.Ordinary.JumpEuler","NSP14.Ordinary.NativeCutH0","NSP14.Ordinary.NativeCutH0Z","NSP14.Ordinary.NativeFullTransfer","NSP14.Ordinary.NumericalBettiClosure","NSP14.Ordinary.RelativeAlgebraRestriction","NSP14.Ordinary.RelativeConeBetti","NSP14.Ordinary.RelativeFinite","NSP14.Ordinary.RelativeInjection","NSP14.Ordinary.RelativeNativeKoszul","NSP14.Ordinary.RelativePresentation","NSP14.Ordinary.RelativeRowsAll","NSP14.Ordinary.RelativeSomeKoszul","NSP14.Ordinary.RelativeTerminal","NSP14.Ordinary.RelativeXComparison","NSP14.Ordinary.TowerCombined","NSP14.Ordinary.TowerEuler","NSP14.Ordinary.TowerGrading","NSP14.Ordinary.TowerH0","NSP14.Ordinary.TowerHarmonic","NSP14.Ordinary.TowerResourceWeights","NSP14.Ordinary.TowerRow","NSP14.Ordinary.TowerTerminal","NSP14.Semigroup.ActualLayersField","NSP14.Semigroup.AlgebraHeadQuotient","NSP14.Semigroup.AlgebraPresentation","NSP14.Semigroup.AlgebraVariableOrder","NSP14.Semigroup.AlgebraXSequences","NSP14.Semigroup.AtomSplit","NSP14.Semigroup.AtomVariableOrder","NSP14.Semigroup.AugmentationBetti","NSP14.Semigroup.CutBasis","NSP14.Semigroup.CutPolynomialInjection","NSP14.Semigroup.CutRetraction","NSP14.Semigroup.HeadConstant","NSP14.Semigroup.HeadFirstOrderAlgebra","NSP14.Semigroup.HeadFirstOrderCoordinates","NSP14.Semigroup.HeadFirstOrderSplit","NSP14.Semigroup.HeadLinearTruncation","NSP14.Semigroup.HeadSquareZeroBetti","NSP14.Semigroup.IntervalCompletion","NSP14.Semigroup.RegularHeadBetti","NSP14.Semigroup.TruncGradingCoordinates","NSP14.Target.APLowerRows","NSP14.Target.BettiEulerConvolution","NSP14.Target.CoefficientComparison","NSP14.Target.IntervalAPBetti","NSP14.Target.IntervalBetti","audit.run15.RemainingGoals","audit.run15_apcone.ClosedGoals","audit.run15_apfoundations.Scope","audit.run15_bclosure.ClosedGoals","audit.run15_closure.ClosedGoals","audit.run15_continuation.ClosedGoals","audit.run15_fulltransfer.ClosedGoals","audit.run15_h0closure.ClosedGoals","audit.run15_ordinary.ClosedGoals","audit.run15_xclosure.ClosedGoals","tests.APKernelWindow","tests.APLowerRows","tests.APResolutionFoundations","tests.ActualTorRow","tests.ArithmeticSequence","tests.ArithmeticSequenceApery","tests.ArithmeticSequenceBetti","tests.ArithmeticSequenceConeBetti","tests.ArithmeticSequenceKernelTor","tests.ArithmeticSequenceMaximalBetti","tests.ArithmeticSequenceOrder","tests.BettiEuler","tests.ChangingOrdinaryClosure","tests.CoefficientComparison","tests.CutBasis","tests.CutFinite","tests.CutPolynomialInjection","tests.CutResidual","tests.FiniteKoszulEuler","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.HeadFirstOrder","tests.IntervalAPBetti","tests.IntervalCompletion","tests.IntrinsicFullTransfer","tests.JumpEuler","tests.KoszulSlots","tests.LinearVariableBetti","tests.LinearVariables","tests.NativeCutH0","tests.OrderedQuotientBasis","tests.OrdinaryClosure","tests.OrdinaryTor","tests.RelativePresentation","tests.RelativeXComparison","tests.Run15Actual","tests.SemigroupAlgebraPresentation","tests.SquareZeroEuler","tests.TowerHarmonic","tests.TwoStepActual","NSP14"]
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
