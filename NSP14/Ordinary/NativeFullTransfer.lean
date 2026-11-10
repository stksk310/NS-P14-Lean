module
public import NSP14.Ordinary.RelativeNativeKoszul
public import NSP14.Homological.CorrectedActionComparison
public import NSP14.Homological.RegularCorrectedComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def nativeComplementVariables : List (S.TangentAlgebra k) :=
  (variableList k (Fin C.complementRank)).map (fun x => C.complementPolynomialToG (MvPolynomial.X x))

noncomputable def nativeExtendedCutComplex : ChainComplex (ModuleCat (S.TangentAlgebra k)) ℕ :=
  (actionOnComplex (S.TangentAlgebra k) C.nativeComplementVariables).obj C.nativeCutComplex

noncomputable abbrev nativeExtendedCoefficientComplex : ChainComplex (ModuleCat k) ℕ :=
  regularExtendedCoefficientComplex k (S.TangentAlgebra k) (Fin C.complementRank)
    C.nativeCutVariables C.complementPolynomialToG (variableList k (Fin C.complementRank))

noncomputable abbrev nativeH0ComplementComplex : ChainComplex (ModuleCat k) ℕ :=
  actionH0SingleCoefficientComplex k (S.TangentAlgebra k) (Fin C.complementRank)
    C.nativeCutVariables C.complementPolynomialToG (variableList k (Fin C.complementRank))

noncomputable def nativeH0ComplementIso :=
  actionH0SingleCoefficientIso k (S.TangentAlgebra k) (Fin C.complementRank)
    C.nativeCutVariables C.complementPolynomialToG (variableList k (Fin C.complementRank))

theorem nativeH0Complement_finite (i : ℕ) : Module.Finite k (C.nativeH0ComplementComplex.homology i) := by
  let := C.nativeCutH0Z_finite
  exact actionH0Canonical_finite k (S.TangentAlgebra k) (Fin C.complementRank)
    C.nativeCutVariables C.complementPolynomialToG i

theorem nativeH0Complement_betti (i : ℕ) :
    Module.finrank k (C.nativeH0ComplementComplex.homology i)=
      if i=0 then 1 else i*(C.complementRank+1).choose (i+1) := by
  let := C.nativeCutH0Z_finite
  have h := actionH0Canonical_betti k (S.TangentAlgebra k) (Fin C.complementRank)
    C.nativeCutVariables C.complementPolynomialToG i
  rw [h]
  by_cases hi : i=0
  · subst i;rw [C.nativeCutH0Z_betti_zero];rfl
  · rw [C.nativeCutH0Z_betti i (by omega),ite_eq_right hi]
end NSP14.NumericalSemigroup.LinearCutData
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

/-- Actual relative Koszul complex followed by all actual complement
variables. Its bound keeps exactly the H0 correction. Intrinsic full
Tor identification by variable change is a separate theorem. -/
theorem nativeFull_corrected_bound (i : ℕ) :
    letI := W.relativeG_finite
    Module.finrank L (W.cut.nativeExtendedCoefficientComplex.homology i) ≤
        (if i=0 then 1 else i*(W.cut.complementRank+1).choose (i+1))+
          binomialTransform W.cut.complementRank
            (fun j => if j=0 then 0 else totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG j) i := by
  let := W.relativeG_finite
  let : ∀ j,Module.Finite L (W.cut.nativeCoefficientCutComplex.homology j) := W.nativeRelativeHomology_finite
  have h := regularCorrectedComparison L (W.source.TangentAlgebra L) (Fin W.cut.complementRank)
    W.cut.nativeCutVariables W.cut.complementPolynomialToG (variableList L (Fin W.cut.complementRank))
    W.cut.nativeH0Complement_finite i
  rw [W.cut.nativeH0Complement_betti] at h
  rw [variableList_length,Fintype.card_fin] at h
  have he : (fun j => if j=0 then 0 else Module.finrank L
      (W.cut.nativeCoefficientCutComplex.homology j))=
      (fun j => if j=0 then 0 else totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG j) := by
    funext j
    split_ifs with hj
    · rfl
    · exact W.nativeRelativeBetti j
  rw [he] at h
  exact h
end NSP14.Ordinary.ActualWitness
