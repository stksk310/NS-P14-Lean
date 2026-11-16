module
public import NSP14
@[expose] public section
open CategoryTheory CategoryTheory.Limits
open NSP14 NSP14.Homological NSP14.Ordinary
open scoped BigOperators
namespace Run15Remaining

/-- Numerical formula alone: not an axiom or an actual Betti theorem. -/
def apPositiveProfile (D : ArithmeticSequence.Data) (i : ℕ) : ℕ :=
  let a := D.v-((D.m-1)%D.v)
  i*D.v.choose (i+1)+
    if i ≤ a then (a+1-i)*D.v.choose (i-1) else (i-a)*D.v.choose i

/-- UNPROVED: GSS quotient Betti ranks on the algebraic AP semigroup ring. -/
def APBettiGoal : Prop := ∀ (D : ArithmeticSequence.Data) (k : Type) [Field k] (i : ℕ),
  1 ≤ i → totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=apPositiveProfile D i

/-- UNPROVED: equality of the two actual Betti sequences, not an algebra
isomorphism between the semigroup ring and its cone. -/
def APConeBettiGoal : Prop := ∀ (D : ArithmeticSequence.Data) (k : Type) [Field k] (i : ℕ),
  totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=
  totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i

/-- UNPROVED: the finite-length, generated-in-one-degree module estimate.
N is an actual support bound, not a hypothesis containing the rank estimate. -/
def HarmonicGoal : Prop := ∀ (k : Type) [Field k] (r : ℕ)
  (M : ModuleCat (VariableRing k (Fin r))) [Module.Finite (VariableRing k (Fin r)) M]
  [Module.Finite k (coefficientModule k (Fin r) M)]
  (G : GradedPolynomialModule k (Fin r) M) (b : ℤ) (N : ℕ),
  Submodule.span (VariableRing k (Fin r))
    (Set.range (fun a : G.piece b => (show M from G.inclusion b a)))=⊤ →
  (∀ t : ℕ,N < t → IsZero (G.piece (b+t))) →
  ∀ j,1 ≤ j ∧ j < r →
    (bettiEuler k (Fin r) M j : ℚ) ≤ ((r-1).choose j : ℚ)*
      ∑ t ∈ Finset.range (N+1),((j : ℚ)/(t+j))*Module.finrank k (G.piece (b+t))

/-- UNPROVED: the top over R, which has r+1 variables. The proved finite-P
module top vanishing is not a proof of this statement about G. -/
def RelativeTerminalGoal : Prop := ∀ (k : Type) [Field k] (W : ActualWitness k),
  letI := W.relativeG_finite
  bettiEuler (InfiniteScalarField k) (Option (Fin W.source.actualCutRank)) W.relativeG
    (W.source.actualCutRank+1)=0

/-- UNPROVED: first x-Koszul comparison and harmonic estimates must be
applied to this witness to obtain this actual row bound. -/
def ActualTorToRowGoal : Prop := ∀ (k : Type) [Field k] (W : ActualWitness k) (j : ℕ),
  letI := W.relativeG_finite
  1 ≤ j ∧ j ≤ W.source.actualCutRank →
  (bettiEuler (InfiniteScalarField k) (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ) ≤
    TargetMargin.lower W.source.embeddingDimension W.source.actualCutRank j+
      (W.source.actualLayers k).row W.source.actualCutRank j W.source.deficit

/-- UNPROVED: coefficient form of the H0-corrected full-variable transfer.
The constant f+1 is removed by starting the R-Betti sum at j=1. -/
def CorrectedFullTransferGoal : Prop := ∀ (k : Type) [Field k] (W : ActualWitness k) (i : ℕ),
  letI := W.relativeG_finite
  let f := W.source.embeddingDimension-W.source.actualCutRank-1
  1 ≤ i →
  (totalBetti (InfiniteScalarField k) W.source.AtomExponent
    (ModuleCat.of (W.source.FullPolynomialRing (InfiniteScalarField k))
      (W.source.TangentAlgebra (InfiniteScalarField k))) i : ℚ) ≤
    Target.positiveOrdinaryCoefficient (f+1) i+
      ∑ j ∈ Finset.range i,(f.choose (i-(j+1)) : ℚ)*
        totalBetti (InfiniteScalarField k) (Option (Fin W.source.actualCutRank)) W.relativeG (j+1)

/-- UNPROVED: no harmonic, Tor-to-row, target, or cut Prop is an argument
of the requested final theorem. -/
def OrdinaryBettiBoundGoal : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k],
  3 ≤ S.embeddingDimension → S.multiplicity-1 ≤ S.width → ∀ i,1 ≤ i →
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i ≤
      i*S.multiplicity.choose (i+1)

/-- UNPROVED: actual completed cones, their own full minimal variable sets,
all rows including zero, over the original arbitrary coefficient field. -/
def OrdinaryActualCompletionGoal : Prop := ∀ (S : NumericalSemigroup) (k : Type) [Field k]
    (he : 3 ≤ S.embeddingDimension),
  let T := S.intervalCompletion (show 2 ≤ S.embeddingDimension from by omega)
  S.multiplicity-1 ≤ S.width → ∀ i,
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k T.AtomExponent (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i
end Run15Remaining
