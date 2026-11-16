module
import NSP14
import all NSP14.Endpoint.CarrySums
import all NSP14.Endpoint.CompetitorBounds
import all NSP14.Endpoint.FiniteCompetitors
import all NSP14.Endpoint.FiniteSocleBounds
import all NSP14.NarrowFour.Comparison
import all NSP14.NarrowFour.CoreWords
import all NSP14.NarrowFour.CubicPayment
import all NSP14.NarrowFour.Distance
import all NSP14.NarrowFour.FirstCount
import all NSP14.NarrowFour.FirstLarge
import all NSP14.NarrowFour.HigherRows
import all NSP14.NarrowFour.Relations
import all NSP14.NarrowFour.SmallWidths
import all NSP14.NarrowFour.SocleTriangle
import all NSP14.NarrowFour.StandardWords
import all NSP14.NarrowFour.WidthFourComparison
import all NSP14.NarrowFour.WidthFourCompetitors
import all NSP14.NarrowFour.WidthFourCore
import all NSP14.NarrowFour.WidthFourInitial
import all NSP14.Semigroup.IntervalCompletionAll
import all NSP14.SmallEmbedding.Base
import all NSP14.SmallEmbedding.LanTuVu
import all NSP14.SmallEmbedding.ThreeComparison
import all NSP14.SmallEmbedding.ThreePresentation
import all NSP14.Width.AntipodalComparison
import all NSP14.Width.DenseComparison
import all NSP14.Width.DenseLexResources
import all NSP14.Width.DensePayment
import all NSP14.Width.FiveHigher
import all NSP14.Width.FiveNonAntipodal
import all NSP14.Width.HigherFromSecond
import all NSP14.Width.IntegerPayment
import all NSP14.Width.SparseHigher
import audit.DomainChecks
import audit.block02.AssumptionChecks
import audit.run14.RemainingGoals
import audit.run14_continuation.ClosedGoals
import audit.run15.RemainingGoals
import audit.run15_apcone.ClosedGoals
import audit.run15_apfoundations.Scope
import audit.run15_bclosure.ClosedGoals
import audit.run15_closure.ClosedGoals
import audit.run15_continuation.ClosedGoals
import audit.run15_fulltransfer.ClosedGoals
import audit.run15_h0closure.ClosedGoals
import audit.run15_ordinary.ClosedGoals
import audit.run15_xclosure.ClosedGoals
import audit.run16.ClosedGoals
import audit.run17.ClosedGoals
import audit.run17.RequestedGoals
import audit.run18.BHPEKClosedGoals
import audit.run18.ClosedGoals
import audit.run18.DenseClosedGoals
import audit.run18.DenseResourcesClosed
import audit.run18.EKClosedGoals
import audit.run18.EdgeClosedGoals
import audit.run18.FiveClosedGoals
import audit.run18.PartialClosedGoals
import audit.run18.RequestedGoals
import audit.run18.acceptance.BHPEK
import audit.run18.acceptance.W_CLOSE
import audit.run18.acceptance.W_DENSE
import audit.run18.acceptance.W_EDGE
import audit.run18.acceptance.W_FIVE
import all audit.run19.ClosedGoals
import all audit.run19.ClosedN4Goals
import all audit.run19.RequestedGoals
import audit.run19.acceptance.I_BASE
import audit.run19.acceptance.I_THREE
import audit.run19.acceptance.N_CLOSE
import audit.run19.acceptance.N_DISTANCE
import audit.run19.acceptance.N_FIRST
import audit.run19.acceptance.N_HIGH
import audit.run19.acceptance.N_SMALL
import audit.run19.acceptance.N_WIDTH4
import audit.run19.acceptance.N_WORDS
import audit.run19.acceptance.X_LTV
import audit.v06_alignment.RouteChecks
import tests.APKernelWindow
import tests.APLowerRows
import tests.APResolutionFoundations
import tests.ActualGradedBaseChange
import tests.ActualSidon
import tests.ActualTorRow
import tests.AntipodalActual
import tests.AperyQuotient
import tests.ArithmeticSequence
import tests.ArithmeticSequenceApery
import tests.ArithmeticSequenceBetti
import tests.ArithmeticSequenceConeBetti
import tests.ArithmeticSequenceKernelTor
import tests.ArithmeticSequenceMaximalBetti
import tests.ArithmeticSequenceOrder
import tests.ArtinGradedChain
import tests.ArtinGradedMaps
import tests.ArtinGradedZero
import tests.BasisBlocks
import tests.BasisGradedScalarComparison
import tests.BasiswiseTensor
import tests.BettiBaseChange
import tests.BettiEuler
import tests.CarrierTransport
import tests.ChangingOrdinaryClosure
import tests.CoefficientComparison
import tests.ColexRestriction
import tests.CompletedComparison
import tests.CutBasis
import tests.CutFinite
import tests.CutPolynomialInjection
import tests.CutResidual
import tests.DegreeFamily
import tests.DegreeSeparator
import tests.DensePayment
import tests.DirectSumSplit
import tests.DistractionChain
import tests.DistractionGraded
import tests.DistractionGradedExamples
import tests.DistractionHilbert
import tests.DistractionIdeal
import tests.DistractionLinearEquiv
import tests.DistractionMonomial
import tests.DistractionTensor
import tests.ElementaryDistraction
import tests.EndpointActualKernel
import tests.EndpointAdditive
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
import tests.ExteriorContraction
import tests.FilteredHomology
import tests.FiniteHilbertProfiles
import tests.FiniteKoszulEuler
import tests.FunctionalMinor
import tests.GenericDistraction
import tests.GenericDistractionBoundary
import tests.GenericDistractionExterior
import tests.GenericDistractionField
import tests.GenericDistractionIteration
import tests.GenericDistractionPrincipal
import tests.GenericDistractionProgress
import tests.GenericDistractionStable
import tests.GenericDistractionStep
import tests.GradedBasis
import tests.GradedIdealAdjoining
import tests.GradedKoszul
import tests.GradedKoszulBasis
import tests.GradedKoszulExact
import tests.GradedKoszulRestriction
import tests.GreenLinearAlgebra
import tests.Harmonic
import tests.HeadFirstOrder
import tests.HomogeneousBasisPieces
import tests.IdealAdjoining
import tests.IdealScalarQuotient
import tests.InitialAction
import tests.InitialBetti
import tests.InitialBoundary
import tests.InitialIdeal
import tests.InitialTransport
import tests.IntervalAPBetti
import tests.IntervalCompletion
import tests.IntrinsicFullTransfer
import tests.JumpBounds
import tests.JumpEuler
import tests.JumpStrata
import tests.KneserActual
import tests.KoszulActual
import tests.KoszulComplex
import tests.KoszulExactness
import tests.KoszulExterior
import tests.KoszulExteriorBasis
import tests.KoszulExteriorContraction
import tests.KoszulExteriorGrading
import tests.KoszulExteriorMap
import tests.KoszulFiniteModules
import tests.KoszulPresentation
import tests.KoszulSlotGrading
import tests.KoszulSlots
import tests.KoszulTor
import tests.KoszulVariableFactor
import all tests.LTVActual
import tests.LargeScalar
import tests.LargeSeed
import tests.LexBetti
import tests.LexCompatibleDegrees
import tests.LexDegreeIdeal
import tests.LexEK
import tests.LexEKOrdinary
import tests.LexGeneratorOrder
import tests.LexGradedStep
import tests.LexHilbert
import tests.LexHilbertExamples
import tests.LexLinearQuotientExamples
import tests.LexLinearQuotients
import tests.LexStable
import tests.LexTailCorrection
import tests.LexTailSupport
import tests.LexUniqueness
import tests.LinearVariableBetti
import tests.LinearVariables
import tests.LowRank
import tests.MinimalResolution
import tests.MonomialExtension
import tests.MonomialExtensionGraded
import tests.MonomialScalarExamples
import all tests.N4ActualClosure
import tests.N4CoreWords
import tests.N4CubicPayment
import tests.N4Distance
import tests.N4First
import all tests.N4Higher
import all tests.N4Small
import all tests.N4StandardWords
import all tests.N4WidthFour
import tests.NativeCutH0
import tests.NormalTriangular
import tests.OffsetStabilization
import tests.OrderedQuotientBasis
import tests.OrdinaryClosure
import tests.OrdinaryNumerical
import tests.OrdinaryTor
import tests.PolynomialAction
import tests.PolynomialBaseChange
import tests.PrefixDominance
import tests.PrefixGeneratorCorrection
import tests.PrefixOrder
import tests.PrefixVariableRestriction
import tests.RankEuler
import tests.RelativePresentation
import tests.RelativeXComparison
import tests.Resources
import tests.Run12Axioms
import tests.Run12BasicExamples
import tests.Run12Fixtures
import tests.Run13Axioms
import tests.Run13ClosureFixtures
import tests.Run13Fixtures
import tests.Run14Acceptance
import tests.Run14Closure
import tests.Run14Fixtures
import tests.Run14Volume
import tests.Run15Actual
import tests.Run17Definitions
import tests.Run17Growth
import tests.Run17SequenceExamples
import tests.Run19Contracts
import tests.SavchevChen
import tests.SemigroupAlgebraPresentation
import tests.SemigroupFoundations
import tests.SemigroupRing
import tests.Sidon
import all tests.SmallEmbeddingBase
import all tests.SmallEmbeddingThree
import tests.SmallScalar
import tests.SmallVariableComparison
import tests.SquareZeroEuler
import tests.StableBettiComparison
import tests.StableBinomialWeights
import tests.StableDegreeDecomposition
import tests.StandardBettiWeights
import tests.StandardMonomials
import tests.StrongStableEK
import tests.StrongStableOperations
import tests.StrongStableRestriction
import tests.SuffixVariableRestriction
import tests.TangentAlgebra
import tests.TorNaturality
import tests.TotalLexBetti
import tests.TowerHarmonic
import tests.TriangularBlockRank
import tests.TwoStepActual
import all tests.V06Dense
import all tests.V06Endpoint
import all tests.V06HigherFromSecond
import all tests.V06IntegerPayment
import tests.VariableIdealBetti
import tests.VariableIdealGraded
import tests.WidthActualClosure
import tests.WidthDense
import tests.WidthDenseResources
import tests.WidthEdgeAP
import tests.WidthEdgeGeneral
import tests.WidthEdgeGeometry
import tests.WidthFive
import tests.WidthFiveHigher
import tests.WidthFiveNonAntipodal
import tests.WidthFiveSmall
import tests.WidthSparse
import tests.WidthSparseCache
import tests.WidthSparseData
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let typed : Array String := #["NSP14.Endpoint.CarrySums","NSP14.Endpoint.CompetitorBounds","NSP14.Endpoint.FiniteCompetitors","NSP14.Endpoint.FiniteSocleBounds","NSP14.NarrowFour.Comparison","NSP14.NarrowFour.CoreWords","NSP14.NarrowFour.CubicPayment","NSP14.NarrowFour.Distance","NSP14.NarrowFour.FirstCount","NSP14.NarrowFour.FirstLarge","NSP14.NarrowFour.HigherRows","NSP14.NarrowFour.Relations","NSP14.NarrowFour.SmallWidths","NSP14.NarrowFour.SocleTriangle","NSP14.NarrowFour.StandardWords","NSP14.NarrowFour.WidthFourComparison","NSP14.NarrowFour.WidthFourCompetitors","NSP14.NarrowFour.WidthFourCore","NSP14.NarrowFour.WidthFourInitial","NSP14.Semigroup.IntervalCompletionAll","NSP14.SmallEmbedding.Base","NSP14.SmallEmbedding.LanTuVu","NSP14.SmallEmbedding.ThreeComparison","NSP14.SmallEmbedding.ThreePresentation","NSP14.Width.AntipodalComparison","NSP14.Width.DenseComparison","NSP14.Width.DenseLexResources","NSP14.Width.DensePayment","NSP14.Width.FiveHigher","NSP14.Width.FiveNonAntipodal","NSP14.Width.HigherFromSecond","NSP14.Width.IntegerPayment","NSP14.Width.SparseHigher","audit.run19.ClosedGoals","audit.run19.ClosedN4Goals","audit.run19.RequestedGoals","tests.LTVActual","tests.N4ActualClosure","tests.N4Higher","tests.N4Small","tests.N4StandardWords","tests.N4WidthFour","tests.SmallEmbeddingBase","tests.SmallEmbeddingThree","tests.V06Dense","tests.V06Endpoint","tests.V06HigherFromSecond","tests.V06IntegerPayment"]
 IO.println ((Json.mkObj [("audit_metadata",toJson true),("imported_modules",toJson (env.header.moduleNames.map Name.toString))]).compress)
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if modName == "NSP14" || modName.startsWith "NSP14." || modName == "tests" || modName.startsWith "tests." || modName.startsWith "audit." then
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
   if typed.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
