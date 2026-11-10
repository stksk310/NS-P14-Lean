module
public import NSP14.Ordinary.RelativeRowsAll
public import NSP14.Target.BettiEulerConvolution
public import NSP14.Homological.ActualCoefficientBaseChange
@[expose] public section
open NSP14.Homological
open scoped BigOperators
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)
local notation "f" => W.cut.complementRank

/-- The existing numerical rows now bound actual intrinsic full Betti
numbers, with H0 correction and every relative top row retained. -/
theorem ordinary_betti_bound_extension (i : ℕ) (hi : 1 ≤ i) :
    totalBetti L W.source.AtomExponent (ModuleCat.of (W.source.FullPolynomialRing L) (W.source.TangentAlgebra L)) i ≤
      i*W.source.multiplicity.choose (i+1) := by
  let := W.relativeG_finite
  let c : ℕ → ℚ := fun j => (bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ)
  have hb (j : ℕ) : (totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) : ℚ)=c (j+1)+c j := by
    have h := bettiEuler_succ L (Option (Fin W.source.actualCutRank)) W.relativeG j
    have hz : (totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) : ℤ)=
        bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1)+
          bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j := by omega
    dsimp only [c]
    exact_mod_cast hz
  have hc0 : c 0=(f+1 : ℕ) := by
    dsimp only [c]
    rw [bettiEuler_zero,W.relativeBetti_zero]
    push_cast
    ring
  have hsum : (∑ j∈Finset.range i,((f).choose (i-(j+1)) : ℚ)*
      totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1))=
      ((f).choose (i-1) : ℚ)*(f+1 : ℕ)+
        ∑ j∈Finset.range i,((f+1).choose (i-(j+1)) : ℚ)*c (j+1) := by
    simp_rw [hb]
    rw [Target.positive_euler_convolution f i hi c,hc0]
  have hsource := W.correctedFullTransfer i hi
  dsimp only at hsource
  rw [← W.cut.complementRank_eq,hsum] at hsource
  have hrows : (∑ j∈Finset.range i,((f+1).choose (i-(j+1)) : ℚ)*c (j+1)) ≤
      ∑ j∈Finset.range i,((f+1).choose (i-(j+1)) : ℚ)*
        TargetMargin.target W.source.embeddingDimension W.source.deficit W.source.actualCutRank (j+1) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (W.actualTor_target_row_all (j+1) (by omega)) (Nat.cast_nonneg _)
  have hemb : 3 ≤ W.source.embeddingDimension := W.embedding
  have hcut := W.source.actualCutRank_le W.embedding
  have heq : W.source.embeddingDimension-W.source.actualCutRank=f+1 := by
    have := W.cut.complementRank_eq
    omega
  have heq' : W.source.embeddingDimension-W.source.actualCutRank+1=f+2 := by omega
  have ht := Target.ordinary_target_difference W.source.embeddingDimension W.source.deficit W.source.actualCutRank i
    (by have := W.source.actualCutRank_two_le;omega) (by omega)
  rw [← W.source.multiplicity_eq_embedding_add_deficit,heq',heq] at ht
  have hh := Target.ordinary_h0_correction f i hi
  have hfinal : (totalBetti L W.source.AtomExponent (ModuleCat.of (W.source.FullPolynomialRing L)
      (W.source.TangentAlgebra L)) i : ℚ) ≤ Target.positiveOrdinaryCoefficient W.source.multiplicity i := by
    nlinarith
  unfold Target.positiveOrdinaryCoefficient at hfinal
  exact_mod_cast hfinal
end NSP14.Ordinary.ActualWitness
namespace NSP14.Ordinary
variable (S : NumericalSemigroup) (k : Type) [Field k]

/-- An ordinary multiplicity capacity bound for every actual source of
embedding dimension at least three, over its original arbitrary field. -/
theorem ordinary_betti_bound (he : 3 ≤ S.embeddingDimension) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i ≤
      i*S.multiplicity.choose (i+1) := by
  let W := canonicalActualWitness S k he
  have h := W.ordinary_betti_bound_extension i hi
  change totalBetti (InfiniteScalarField k) S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing (InfiniteScalarField k)) (S.TangentAlgebra (InfiniteScalarField k))) i ≤
      i*S.multiplicity.choose (i+1) at h
  rw [S.actualG_totalBetti_baseChange k (InfiniteScalarField k) i] at h
  exact h
end NSP14.Ordinary
