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
import tests.CarrierTransport
import tests.EndpointActualKernel
import tests.EndpointArtinRank
import tests.EndpointArtinRefinements
import tests.EndpointBoundaryExamples
import tests.EndpointCarry
import tests.EndpointCompensation
import tests.EndpointCompetitorBounds
import tests.EndpointCompetitors
import tests.EndpointComputedExamples
import tests.EndpointConeBalance
import tests.EndpointCoordinates
import tests.EndpointCore
import tests.EndpointCoreArtin
import tests.EndpointCoreGrading
import tests.EndpointData
import tests.EndpointFiberModule
import tests.EndpointFibers
import tests.EndpointFirstBetti
import tests.EndpointHomology
import tests.EndpointIdealGenerators
import tests.EndpointInternalCoordinates
import tests.EndpointInternalSocle
import tests.EndpointMinimal
import tests.EndpointMinimalBounds
import tests.EndpointModules
import tests.EndpointNativeTransfer
import tests.EndpointNilpotence
import tests.EndpointNonmonomial
import tests.EndpointNormalization
import tests.EndpointOrientation
import tests.EndpointPresentation
import tests.EndpointQuadratic
import tests.EndpointQuotient
import tests.EndpointResidues
import tests.EndpointRhat
import tests.EndpointRowPackage
import tests.EndpointRows
import tests.EndpointSocle
import tests.EndpointSoclePoints
import tests.EndpointStandardArtin
import tests.EndpointStopping
import tests.EndpointSurvivingBasis
import tests.EndpointTwoMonomial
import tests.EndpointTwoVariables
import tests.EndpointVolume
import tests.EndpointWords
import audit.run16.ClosedGoals
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.SmallScalar","tests.Sidon","tests.Resources","tests.LowRank","tests.LargeSeed","tests.LargeScalar","tests.OrdinaryNumerical","tests.SemigroupFoundations","tests.SemigroupRing","tests.TangentAlgebra","tests.AperyQuotient","tests.Run12BasicExamples","tests.Run12Fixtures","tests.JumpBounds","tests.PolynomialAction","tests.JumpStrata","tests.CompletedComparison","tests.Run12Axioms","tests.Run13Fixtures","tests.ActualGradedBaseChange","tests.BettiBaseChange","tests.FilteredHomology","tests.GradedKoszul","tests.KoszulActual","tests.KoszulComplex","tests.KoszulExactness","tests.KoszulFiniteModules","tests.KoszulPresentation","tests.KoszulTor","tests.MinimalResolution","tests.PolynomialBaseChange","tests.RankEuler","tests.Run13ClosureFixtures","tests.StandardMonomials","tests.TorNaturality","audit.DomainChecks","audit.block02.AssumptionChecks","tests.Run14Fixtures","tests.ActualSidon","tests.OffsetStabilization","tests.Run14Acceptance","audit.run14.RemainingGoals","tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals","tests.ArithmeticSequenceMaximalBetti","tests.ArithmeticSequenceConeBetti","tests.APKernelWindow","tests.APLowerRows","tests.APResolutionFoundations","tests.ActualTorRow","tests.ArithmeticSequence","tests.ArithmeticSequenceApery","tests.ArithmeticSequenceBetti","tests.ArithmeticSequenceKernelTor","tests.ArithmeticSequenceOrder","tests.BettiEuler","tests.ChangingOrdinaryClosure","tests.CoefficientComparison","tests.CutBasis","tests.CutFinite","tests.CutPolynomialInjection","tests.TowerHarmonic","tests.CutResidual","tests.FiniteKoszulEuler","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.HeadFirstOrder","tests.IntervalAPBetti","tests.IntervalCompletion","tests.IntrinsicFullTransfer","tests.JumpEuler","tests.KoszulSlots","tests.LinearVariableBetti","tests.LinearVariables","tests.NativeCutH0","tests.OrderedQuotientBasis","tests.OrdinaryClosure","tests.OrdinaryTor","tests.RelativePresentation","tests.RelativeXComparison","tests.Run13Axioms","tests.Run15Actual","tests.SemigroupAlgebraPresentation","tests.SquareZeroEuler","tests.TwoStepActual","audit.run15.RemainingGoals","audit.run15_continuation.ClosedGoals","audit.run15_xclosure.ClosedGoals","audit.run15_bclosure.ClosedGoals","audit.run15_h0closure.ClosedGoals","audit.run15_fulltransfer.ClosedGoals","audit.run15_ordinary.ClosedGoals","audit.run15_apcone.ClosedGoals","audit.run15_apfoundations.Scope","audit.run15_closure.ClosedGoals","tests.CarrierTransport","tests.EndpointActualKernel","tests.EndpointArtinRank","tests.EndpointArtinRefinements","tests.EndpointBoundaryExamples","tests.EndpointCarry","tests.EndpointCompensation","tests.EndpointCompetitorBounds","tests.EndpointCompetitors","tests.EndpointComputedExamples","tests.EndpointConeBalance","tests.EndpointCoordinates","tests.EndpointCore","tests.EndpointCoreArtin","tests.EndpointCoreGrading","tests.EndpointData","tests.EndpointFiberModule","tests.EndpointFibers","tests.EndpointFirstBetti","tests.EndpointHomology","tests.EndpointIdealGenerators","tests.EndpointInternalCoordinates","tests.EndpointInternalSocle","tests.EndpointMinimal","tests.EndpointMinimalBounds","tests.EndpointModules","tests.EndpointNativeTransfer","tests.EndpointNilpotence","tests.EndpointNonmonomial","tests.EndpointNormalization","tests.EndpointOrientation","tests.EndpointPresentation","tests.EndpointQuadratic","tests.EndpointQuotient","tests.EndpointResidues","tests.EndpointRhat","tests.EndpointRowPackage","tests.EndpointRows","tests.EndpointSocle","tests.EndpointSoclePoints","tests.EndpointStandardArtin","tests.EndpointStopping","tests.EndpointSurvivingBasis","tests.EndpointTwoMonomial","tests.EndpointTwoVariables","tests.EndpointVolume","tests.EndpointWords","audit.run16.ClosedGoals"]
 let newModules : Array String := #["NSP14.Endpoint.ActualKernel","NSP14.Endpoint.AdjacentCorners","NSP14.Endpoint.Antichains","NSP14.Endpoint.ArtinQuotient","NSP14.Endpoint.ArtinRank","NSP14.Endpoint.ArtinTransport","NSP14.Endpoint.ArtinWeights","NSP14.Endpoint.AssembledKernel","NSP14.Endpoint.AssemblyCoefficients","NSP14.Endpoint.BasisGrading","NSP14.Endpoint.Carry","NSP14.Endpoint.CarrySums","NSP14.Endpoint.Compensation","NSP14.Endpoint.CompetitorBounds","NSP14.Endpoint.Competitors","NSP14.Endpoint.ConeBalance","NSP14.Endpoint.CoordinateIdeals","NSP14.Endpoint.Coordinates","NSP14.Endpoint.Core","NSP14.Endpoint.CoreArtinBasis","NSP14.Endpoint.CoreArtinIdeal","NSP14.Endpoint.CoreAugmentation","NSP14.Endpoint.CoreGeneration","NSP14.Endpoint.CoreGrading","NSP14.Endpoint.CoreHilbert","NSP14.Endpoint.CoreHilbertSum","NSP14.Endpoint.CoreInternalAction","NSP14.Endpoint.CoreInternalPresentation","NSP14.Endpoint.CoreKernel","NSP14.Endpoint.CoreLowDegrees","NSP14.Endpoint.CoreMap","NSP14.Endpoint.CoreRelations","NSP14.Endpoint.CoreWeights","NSP14.Endpoint.CoreWords","NSP14.Endpoint.Corners","NSP14.Endpoint.Data","NSP14.Endpoint.EndpointCoordinateSteps","NSP14.Endpoint.EndpointRank","NSP14.Endpoint.FiberAction","NSP14.Endpoint.FiberAssembly","NSP14.Endpoint.FiberIndices","NSP14.Endpoint.FiberInjection","NSP14.Endpoint.FiberModule","NSP14.Endpoint.Fibers","NSP14.Endpoint.FiniteCompetitors","NSP14.Endpoint.FiniteMinima","NSP14.Endpoint.FiniteOrder","NSP14.Endpoint.FiniteSocle","NSP14.Endpoint.FiniteSocleBounds","NSP14.Endpoint.FiniteSocleWindow","NSP14.Endpoint.FiniteSurvivors","NSP14.Endpoint.FiniteWords","NSP14.Endpoint.FirstHarmonic","NSP14.Endpoint.FirstRow","NSP14.Endpoint.FiveBound","NSP14.Endpoint.FullTransfer","NSP14.Endpoint.H0Internal","NSP14.Endpoint.HomologyBalance","NSP14.Endpoint.HomologyFinite","NSP14.Endpoint.IdealBasis","NSP14.Endpoint.IdealCoordinates","NSP14.Endpoint.InternalCoordinates","NSP14.Endpoint.InternalMonoid","NSP14.Endpoint.InternalSocleBasis","NSP14.Endpoint.KernelIdeals","NSP14.Endpoint.Minimal","NSP14.Endpoint.MinimalBounds","NSP14.Endpoint.MinimalGenerators","NSP14.Endpoint.MinimalPredecessors","NSP14.Endpoint.MinimalWords","NSP14.Endpoint.Modules","NSP14.Endpoint.MonomialAnnihilator","NSP14.Endpoint.MonomialCoordinates","NSP14.Endpoint.MonomialQuotient","NSP14.Endpoint.MonomialSocle","NSP14.Endpoint.NativeTransfer","NSP14.Endpoint.Nilpotence","NSP14.Endpoint.Normalization","NSP14.Endpoint.OffsetOrder","NSP14.Endpoint.PartialBasisKernel","NSP14.Endpoint.PositiveRows","NSP14.Endpoint.Presentation","NSP14.Endpoint.QuadraticDimension","NSP14.Endpoint.Quotient","NSP14.Endpoint.QuotientBound","NSP14.Endpoint.Residues","NSP14.Endpoint.RowPackage","NSP14.Endpoint.SingleAction","NSP14.Endpoint.Socle","NSP14.Endpoint.SocleBounds","NSP14.Endpoint.SocleCorePoints","NSP14.Endpoint.SocleCorners","NSP14.Endpoint.SocleInjection","NSP14.Endpoint.SoclePoints","NSP14.Endpoint.StandardArtinAugmentation","NSP14.Endpoint.StandardArtinFinite","NSP14.Endpoint.StandardArtinGeneration","NSP14.Endpoint.StandardArtinGenerators","NSP14.Endpoint.StandardArtinGrading","NSP14.Endpoint.StandardArtinLow","NSP14.Endpoint.StandardArtinQuadratic","NSP14.Endpoint.StandardArtinRows","NSP14.Endpoint.StandardHomogeneous","NSP14.Endpoint.Stopping","NSP14.Endpoint.SurvivingBasis","NSP14.Endpoint.SurvivingKernel","NSP14.Endpoint.TwoActionTop","NSP14.Endpoint.TwoInternal","NSP14.Endpoint.TwoMonomial","NSP14.Endpoint.TwoRows","NSP14.Endpoint.TwoScalarSocle","NSP14.Endpoint.VariableOrder","NSP14.Endpoint.Volume","NSP14.Endpoint.XHomology","NSP14.Semigroup.CarrierTransport","NSP14.Semigroup.WidthNormalization","tests.CarrierTransport","tests.EndpointActualKernel","tests.EndpointArtinRank","tests.EndpointArtinRefinements","tests.EndpointBoundaryExamples","tests.EndpointCarry","tests.EndpointCompensation","tests.EndpointCompetitorBounds","tests.EndpointCompetitors","tests.EndpointComputedExamples","tests.EndpointConeBalance","tests.EndpointCoordinates","tests.EndpointCore","tests.EndpointCoreArtin","tests.EndpointCoreGrading","tests.EndpointData","tests.EndpointFiberModule","tests.EndpointFibers","tests.EndpointFirstBetti","tests.EndpointHomology","tests.EndpointIdealGenerators","tests.EndpointInternalCoordinates","tests.EndpointInternalSocle","tests.EndpointMinimal","tests.EndpointMinimalBounds","tests.EndpointModules","tests.EndpointNativeTransfer","tests.EndpointNilpotence","tests.EndpointNonmonomial","tests.EndpointNormalization","tests.EndpointOrientation","tests.EndpointPresentation","tests.EndpointQuadratic","tests.EndpointQuotient","tests.EndpointResidues","tests.EndpointRhat","tests.EndpointRowPackage","tests.EndpointRows","tests.EndpointSocle","tests.EndpointSoclePoints","tests.EndpointStandardArtin","tests.EndpointStopping","tests.EndpointSurvivingBasis","tests.EndpointTwoMonomial","tests.EndpointTwoVariables","tests.EndpointVolume","tests.EndpointWords","audit.run16.ClosedGoals","NSP14"]
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
