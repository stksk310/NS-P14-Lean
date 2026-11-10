module
public import NSP14.Ordinary.FullVariableOrder
public import NSP14.Homological.PositiveBinomial
public import NSP14.Target.CoefficientComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- The native all-variable complex computes ordinary intrinsic Tor in the
actual minimal presentation. The arbitrary linear basis change is accounted for. -/
theorem nativeExtended_intrinsic_betti (i : ℕ) :
    Module.finrank k (C.nativeExtendedCoefficientComplex.homology i)=
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i := by
  let : Module.Finite (VariableRing k (Option (Fin (S.actualCutRank+C.complementRank))))
      (polynomialRegularModule k _ (S.TangentAlgebra k) C.extendedFullToG) := C.extendedFullG_finite
  have h := regularExtendedPolynomialBetti (S.TangentAlgebra k) k (Fin C.complementRank)
    (Option (Fin (S.actualCutRank+C.complementRank))) C.nativeCutVariables C.complementPolynomialToG
    (variableList k (Fin C.complementRank)) C.extendedFullToG C.extendedVariableOrder
    C.extendedVariableOrder_action C.extendedVariableOrder_all C.extendedVariableOrder_nodup i
  exact h.trans (C.extendedFullG_totalBetti i)
end NSP14.NumericalSemigroup.LinearCutData
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

/-- H0-corrected comparison for actual intrinsic full Betti numbers,
including the original full e-variable minimal presentation. -/
theorem correctedFullTransfer_nat (i : ℕ) (hi : 1 ≤ i) :
    letI := W.relativeG_finite
    totalBetti L W.source.AtomExponent (ModuleCat.of (W.source.FullPolynomialRing L) (W.source.TangentAlgebra L)) i ≤
      i*(W.cut.complementRank+1).choose (i+1)+
        ∑ j∈Finset.range i,W.cut.complementRank.choose (i-(j+1))*
          totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) := by
  let := W.relativeG_finite
  have h := W.nativeFull_corrected_bound i
  rw [W.cut.nativeExtended_intrinsic_betti,ite_eq_right (by omega : i≠0),binomialTransform_positive] at h
  exact h

theorem correctedFullTransfer (i : ℕ) (hi : 1 ≤ i) :
    letI := W.relativeG_finite
    let f := W.source.embeddingDimension-W.source.actualCutRank-1
    (totalBetti L W.source.AtomExponent (ModuleCat.of (W.source.FullPolynomialRing L) (W.source.TangentAlgebra L)) i : ℚ) ≤
      Target.positiveOrdinaryCoefficient (f+1) i+
        ∑ j∈Finset.range i,(f.choose (i-(j+1)) : ℚ)*
          totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) := by
  let := W.relativeG_finite
  dsimp only
  rw [← W.cut.complementRank_eq]
  have h := W.correctedFullTransfer_nat i hi
  unfold Target.positiveOrdinaryCoefficient
  exact_mod_cast h
end NSP14.Ordinary.ActualWitness
