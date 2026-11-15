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
import tests.EndpointAdditive
import tests.KneserActual
import tests.Run17Definitions
import tests.Run17Growth
import tests.Run17SequenceExamples
import tests.SavchevChen
import audit.run17.RequestedGoals
import audit.run17.ClosedGoals
import audit.run18.RequestedGoals
import audit.run18.DenseResourcesClosed
import audit.run18.EKClosedGoals
import audit.run18.EdgeClosedGoals
import audit.run18.FiveClosedGoals
import audit.run18.PartialClosedGoals
import audit.run18.acceptance.W_EDGE
import audit.run18.acceptance.W_FIVE
import tests.WidthFiveHigher
import tests.AntipodalActual
import tests.ArtinGradedChain
import tests.ArtinGradedMaps
import tests.ArtinGradedZero
import tests.BasisBlocks
import tests.DirectSumSplit
import tests.DistractionHilbert
import tests.DistractionIdeal
import tests.DistractionLinearEquiv
import tests.DistractionMonomial
import tests.GenericDistraction
import tests.GenericDistractionField
import tests.GradedIdealAdjoining
import tests.GradedKoszulBasis
import tests.GradedKoszulExact
import tests.GradedKoszulRestriction
import tests.HomogeneousBasisPieces
import tests.IdealAdjoining
import tests.IdealScalarQuotient
import tests.InitialAction
import tests.InitialBetti
import tests.InitialBoundary
import tests.InitialIdeal
import tests.InitialTransport
import tests.KoszulSlotGrading
import tests.KoszulVariableFactor
import tests.LexEK
import tests.LexEKOrdinary
import tests.LexGeneratorOrder
import tests.LexGradedStep
import tests.LexLinearQuotientExamples
import tests.LexLinearQuotients
import tests.LexStable
import tests.NormalTriangular
import tests.TriangularBlockRank
import tests.VariableIdealBetti
import tests.VariableIdealGraded
import tests.WidthDenseResources
import tests.WidthEdgeAP
import tests.WidthEdgeGeneral
import tests.WidthEdgeGeometry
import tests.WidthFive
import tests.WidthFiveNonAntipodal
import tests.WidthFiveSmall
import tests.WidthSparseData
import tests.WidthSparseCache
import tests.WidthSparse
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.SmallScalar","tests.Sidon","tests.Resources","tests.LowRank","tests.LargeSeed","tests.LargeScalar","tests.OrdinaryNumerical","tests.SemigroupFoundations","tests.SemigroupRing","tests.TangentAlgebra","tests.AperyQuotient","tests.Run12BasicExamples","tests.Run12Fixtures","tests.JumpBounds","tests.PolynomialAction","tests.JumpStrata","tests.CompletedComparison","tests.Run12Axioms","tests.Run13Fixtures","tests.ActualGradedBaseChange","tests.BettiBaseChange","tests.FilteredHomology","tests.GradedKoszul","tests.KoszulActual","tests.KoszulComplex","tests.KoszulExactness","tests.KoszulFiniteModules","tests.KoszulPresentation","tests.KoszulTor","tests.MinimalResolution","tests.PolynomialBaseChange","tests.RankEuler","tests.Run13ClosureFixtures","tests.StandardMonomials","tests.TorNaturality","audit.DomainChecks","audit.block02.AssumptionChecks","tests.Run14Fixtures","tests.ActualSidon","tests.OffsetStabilization","tests.Run14Acceptance","audit.run14.RemainingGoals","tests.GreenLinearAlgebra","tests.Run14Closure","tests.Run14Volume","audit.run14_continuation.ClosedGoals","tests.ArithmeticSequenceMaximalBetti","tests.ArithmeticSequenceConeBetti","tests.APKernelWindow","tests.APLowerRows","tests.APResolutionFoundations","tests.ActualTorRow","tests.ArithmeticSequence","tests.ArithmeticSequenceApery","tests.ArithmeticSequenceBetti","tests.ArithmeticSequenceKernelTor","tests.ArithmeticSequenceOrder","tests.BettiEuler","tests.ChangingOrdinaryClosure","tests.CoefficientComparison","tests.CutBasis","tests.CutFinite","tests.CutPolynomialInjection","tests.TowerHarmonic","tests.CutResidual","tests.FiniteKoszulEuler","tests.FunctionalMinor","tests.GradedBasis","tests.Harmonic","tests.HeadFirstOrder","tests.IntervalAPBetti","tests.IntervalCompletion","tests.IntrinsicFullTransfer","tests.JumpEuler","tests.KoszulSlots","tests.LinearVariableBetti","tests.LinearVariables","tests.NativeCutH0","tests.OrderedQuotientBasis","tests.OrdinaryClosure","tests.OrdinaryTor","tests.RelativePresentation","tests.RelativeXComparison","tests.Run13Axioms","tests.Run15Actual","tests.SemigroupAlgebraPresentation","tests.SquareZeroEuler","tests.TwoStepActual","audit.run15.RemainingGoals","audit.run15_continuation.ClosedGoals","audit.run15_xclosure.ClosedGoals","audit.run15_bclosure.ClosedGoals","audit.run15_h0closure.ClosedGoals","audit.run15_fulltransfer.ClosedGoals","audit.run15_ordinary.ClosedGoals","audit.run15_apcone.ClosedGoals","audit.run15_apfoundations.Scope","audit.run15_closure.ClosedGoals","tests.CarrierTransport","tests.EndpointActualKernel","tests.EndpointArtinRank","tests.EndpointArtinRefinements","tests.EndpointBoundaryExamples","tests.EndpointCarry","tests.EndpointCompensation","tests.EndpointCompetitorBounds","tests.EndpointCompetitors","tests.EndpointComputedExamples","tests.EndpointConeBalance","tests.EndpointCoordinates","tests.EndpointCore","tests.EndpointCoreArtin","tests.EndpointCoreGrading","tests.EndpointData","tests.EndpointFiberModule","tests.EndpointFibers","tests.EndpointFirstBetti","tests.EndpointHomology","tests.EndpointIdealGenerators","tests.EndpointInternalCoordinates","tests.EndpointInternalSocle","tests.EndpointMinimal","tests.EndpointMinimalBounds","tests.EndpointModules","tests.EndpointNativeTransfer","tests.EndpointNilpotence","tests.EndpointNonmonomial","tests.EndpointNormalization","tests.EndpointOrientation","tests.EndpointPresentation","tests.EndpointQuadratic","tests.EndpointQuotient","tests.EndpointResidues","tests.EndpointRhat","tests.EndpointRowPackage","tests.EndpointRows","tests.EndpointSocle","tests.EndpointSoclePoints","tests.EndpointStandardArtin","tests.EndpointStopping","tests.EndpointSurvivingBasis","tests.EndpointTwoMonomial","tests.EndpointTwoVariables","tests.EndpointVolume","tests.EndpointWords","audit.run16.ClosedGoals","tests.EndpointAdditive","tests.KneserActual","tests.Run17Definitions","tests.Run17Growth","tests.Run17SequenceExamples","tests.SavchevChen","audit.run17.RequestedGoals","audit.run17.ClosedGoals","audit.run18.RequestedGoals","audit.run18.DenseResourcesClosed","audit.run18.EKClosedGoals","audit.run18.EdgeClosedGoals","audit.run18.FiveClosedGoals","audit.run18.PartialClosedGoals","audit.run18.acceptance.W_EDGE","audit.run18.acceptance.W_FIVE","tests.WidthFiveHigher","tests.AntipodalActual","tests.ArtinGradedChain","tests.ArtinGradedMaps","tests.ArtinGradedZero","tests.BasisBlocks","tests.DirectSumSplit","tests.DistractionHilbert","tests.DistractionIdeal","tests.DistractionLinearEquiv","tests.DistractionMonomial","tests.GenericDistraction","tests.GenericDistractionField","tests.GradedIdealAdjoining","tests.GradedKoszulBasis","tests.GradedKoszulExact","tests.GradedKoszulRestriction","tests.HomogeneousBasisPieces","tests.IdealAdjoining","tests.IdealScalarQuotient","tests.InitialAction","tests.InitialBetti","tests.InitialBoundary","tests.InitialIdeal","tests.InitialTransport","tests.KoszulSlotGrading","tests.KoszulVariableFactor","tests.LexEK","tests.LexEKOrdinary","tests.LexGeneratorOrder","tests.LexGradedStep","tests.LexLinearQuotientExamples","tests.LexLinearQuotients","tests.LexStable","tests.NormalTriangular","tests.TriangularBlockRank","tests.VariableIdealBetti","tests.VariableIdealGraded","tests.WidthDenseResources","tests.WidthEdgeAP","tests.WidthEdgeGeneral","tests.WidthEdgeGeometry","tests.WidthFive","tests.WidthFiveNonAntipodal","tests.WidthFiveSmall","tests.WidthSparseData","tests.WidthSparseCache","tests.WidthSparse"]
 let newModules : Array String := #["NSP14.Endpoint.ArtinGradedChain","NSP14.Endpoint.ArtinGradedMaps","NSP14.Endpoint.ArtinGradedZero","NSP14.Endpoint.ArtinShift","NSP14.Endpoint.GradedIdealAdjoining","NSP14.Endpoint.InitialAction","NSP14.Endpoint.InitialBoundary","NSP14.Endpoint.InitialDiagonal","NSP14.Endpoint.InitialTransport","NSP14.Endpoint.VariableIdealGraded","NSP14.Homological.BasisBlocks","NSP14.Homological.DirectSumSplit","NSP14.Homological.GradedKoszulBasis","NSP14.Homological.GradedKoszulExact","NSP14.Homological.GradedKoszulMap","NSP14.Homological.GradedKoszulPieces","NSP14.Homological.GradedKoszulSplit","NSP14.Homological.HomogeneousBasisPieces","NSP14.Homological.IdealAdjoining","NSP14.Homological.IdealAdjoiningKoszul","NSP14.Homological.IdealScalarQuotient","NSP14.Homological.KoszulCombinedMinor","NSP14.Homological.KoszulSlotGrading","NSP14.Homological.NormalTriangular","NSP14.Homological.TriangularBlockRank","NSP14.Homological.VariableIdealBetti","NSP14.Homological.VariableIdealReduction","NSP14.Lex.DistractionHilbert","NSP14.Lex.DistractionIdeal","NSP14.Lex.DistractionLinearEquiv","NSP14.Lex.DistractionMonomial","NSP14.Lex.EliahouKervaire","NSP14.Lex.EliahouKervaireOrdinary","NSP14.Lex.EliahouKervaireStep","NSP14.Lex.GeneratorOrder","NSP14.Lex.GenericDistraction","NSP14.Lex.GenericDistractionField","NSP14.Lex.Hilbert","NSP14.Lex.Ideal","NSP14.Lex.InitialBetti","NSP14.Lex.InitialIdeal","NSP14.Lex.LinearQuotients","NSP14.Lex.MonomialGenerators","NSP14.Lex.Stable","NSP14.Width.AntipodalBasis","NSP14.Width.AntipodalComparison","NSP14.Width.AntipodalCore","NSP14.Width.AntipodalIdeal","NSP14.Width.AntipodalPresentation","NSP14.Width.AntipodalVolume","NSP14.Width.BinaryMonomialPower","NSP14.Width.CoreIdealPresentation","NSP14.Width.DenseHeight","NSP14.Width.DenseResources","NSP14.Width.DenseVolume","NSP14.Width.EdgeAP","NSP14.Width.EdgeHoleAction","NSP14.Width.EdgeHoleComparison","NSP14.Width.EdgeHoleCounting","NSP14.Width.EdgeHoleGeometry","NSP14.Width.EdgeHoleMinor","NSP14.Width.EdgeHoleResources","NSP14.Width.EdgeHoleWedgeCount","NSP14.Width.FirstResources","NSP14.Width.FiveComparison","NSP14.Width.FiveHigher","NSP14.Width.FiveHoleClassification","NSP14.Width.FiveHoleComparison","NSP14.Width.FiveHoleCore","NSP14.Width.FiveHoleEdge","NSP14.Width.FiveHoleKernel","NSP14.Width.FiveHoleTopRank","NSP14.Width.FiveNonAntipodal","NSP14.Width.FiveSmall","NSP14.Width.IdealGeneratorBound","NSP14.Width.NormalizedCapacity","NSP14.Width.Progression","NSP14.Width.SourceNormalization","NSP14.Width.SparseComparison","NSP14.Width.SparseFirst","NSP14.Width.SparseFirstLarge","NSP14.Width.SparseFirstSmall","NSP14.Width.SparseHigher","NSP14.Width.SparseRemainder","NSP14.Width.SparseSecond","NSP14.Width.SparseVolume","NSP14.Width.TripleCorePoint","audit.run18.DenseResourcesClosed","audit.run18.EKClosedGoals","audit.run18.EdgeClosedGoals","audit.run18.FiveClosedGoals","audit.run18.PartialClosedGoals","audit.run18.RequestedGoals","audit.run18.acceptance.W_EDGE","audit.run18.acceptance.W_FIVE","tests.AntipodalActual","tests.ArtinGradedChain","tests.ArtinGradedMaps","tests.ArtinGradedZero","tests.BasisBlocks","tests.DirectSumSplit","tests.DistractionHilbert","tests.DistractionIdeal","tests.DistractionLinearEquiv","tests.DistractionMonomial","tests.GenericDistraction","tests.GenericDistractionField","tests.GradedIdealAdjoining","tests.GradedKoszulBasis","tests.GradedKoszulExact","tests.GradedKoszulRestriction","tests.HomogeneousBasisPieces","tests.IdealAdjoining","tests.IdealScalarQuotient","tests.InitialAction","tests.InitialBetti","tests.InitialBoundary","tests.InitialIdeal","tests.InitialTransport","tests.KoszulSlotGrading","tests.KoszulVariableFactor","tests.LexEK","tests.LexEKOrdinary","tests.LexGeneratorOrder","tests.LexGradedStep","tests.LexLinearQuotientExamples","tests.LexLinearQuotients","tests.LexStable","tests.NormalTriangular","tests.TriangularBlockRank","tests.VariableIdealBetti","tests.VariableIdealGraded","tests.WidthDenseResources","tests.WidthEdgeAP","tests.WidthEdgeGeneral","tests.WidthEdgeGeometry","tests.WidthFive","tests.WidthFiveHigher","tests.WidthFiveNonAntipodal","tests.WidthFiveSmall","tests.WidthSparse","tests.WidthSparseCache","tests.WidthSparseData","NSP14"]
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
   let mut fields := [("name",toJson n.toString),("module",toJson modName),("kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if newModules.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
