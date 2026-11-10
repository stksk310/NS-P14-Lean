module

public import NSP14

@[expose] public section

open scoped Classical BigOperators
open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary NSP14.Homological

/-! These are definitions of UNPROVED propositions, not theorem declarations,
axioms, or fields supplied to a constructor. No production theorem imports this file. -/
namespace Run14Remaining

noncomputable def linearPolynomial (S : NumericalSemigroup) (k : Type) [Field k]
    (c : S.NonXAtom → k) : S.PolynomialRing k :=
  ∑ a : S.NonXAtom, MvPolynomial.C (c a) * MvPolynomial.X a

noncomputable def partialCutIdeal (S : NumericalSemigroup) (k : Type) [Field k]
    (p : ℕ) (c : Fin p → S.NonXAtom → k) (s : ℕ) : Ideal (S.HeadAlgebra k) :=
  Ideal.span {a | ∃ i : Fin p, i.val < s ∧ a = S.polynomialToA k (linearPolynomial S k (c i))}

noncomputable def cutDegree (S : NumericalSemigroup) (k : Type) [Field k]
    (p : ℕ) (c : Fin p → S.NonXAtom → k) (s n : ℕ) :
    Submodule k (S.HeadAlgebra k ⧸ partialCutIdeal S k p c s) :=
  (S.headDegree k n).map (Ideal.Quotient.mkₐ k (partialCutIdeal S k p c s)).toLinearMap

/-- Still unproved: the exact iterated degree-two Green bound. -/
def GreenDegreeTwoGoal (S : NumericalSemigroup) (k : Type) [Field k] : Prop :=
  Infinite k →
  let a := (S.degreeSet 2).card
  let p := quadraticIndex a
  ∃ c : Fin p → S.NonXAtom → k, LinearIndependent k c ∧
    ∀ s, s ≤ p → Module.finrank k (cutDegree S k p c s 2) ≤
      (p + 1 - s).choose 2 + (a - quadraticTriangular p - s)

/-- Still unproved: one independent cut over a fixed same-characteristic infinite extension. -/
def OneCutGoal (S : NumericalSemigroup) (k : Type) [Field k] : Prop :=
  3 ≤ S.embeddingDimension →
  ∃ c : Fin S.actualCutRank → S.NonXAtom → InfiniteScalarField k,
    LinearIndependent (InfiniteScalarField k) c ∧
    ∀ n, 2 ≤ n → ∀ a ∈ S.headDegree (InfiniteScalarField k) n,
      a ∈ partialCutIdeal S (InfiniteScalarField k) S.actualCutRank c S.actualCutRank

/-- Still unproved: the sharp volume, stronger than the proved cycle-free length bound. -/
def SharpOffsetVolumeGoal (S : NumericalSemigroup) : Prop :=
  (∑ r ∈ (Finset.univ : Finset (Fin S.multiplicity)).filter (fun r => r.val ≠ 0),
      ((S.offsetLevel r - 1 : ℕ) : ℚ)) ≤
    (S.deficit : ℚ) * SmallScalar.volume S.embeddingDimension S.deficit

/-- Still unproved: the simultaneous inequalities on this particular actual H. -/
def ResourceBoundsGoal (S : NumericalSemigroup) (k : Type) [Field k] : Prop :=
  (S.actualLayers k).mass S.deficit ≤
      (S.deficit : ℚ) * SmallScalar.volume S.embeddingDimension S.deficit ∧
  (∀ t, S.towerResource k t ≤ S.multiplicity - 1) ∧
  (S.towerResource k 1 : ℚ) ≤ (S.actualCutRank : ℚ) * S.deficit ∧
  (3 ≤ S.actualCutRank → (S.towerResource k 1 : ℚ) ≤
    (S.multiplicity : ℚ) - 1 - ((S.actualCutRank + 1).choose 2 : ℕ))

/-- Still unproved: actual Data, with the already constructed actual layers fixed. -/
def ActualNumericalDataGoal (S : NumericalSemigroup) (k : Type) [Field k] : Prop :=
  3 ≤ S.embeddingDimension →
    ∃ D : NumericalClosure.Data S.actualCutRank S.embeddingDimension S.deficit,
      D.layers = S.actualLayers k

end Run14Remaining
