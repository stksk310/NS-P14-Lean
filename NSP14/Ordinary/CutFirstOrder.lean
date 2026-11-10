module
public import NSP14.Semigroup.HeadFirstOrderCoordinates
public import NSP14.Ordinary.CutFinite
public import NSP14.Homological.BettiEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutHeadHigh : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.highIdeal k 2))
noncomputable def cutB : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.FirstOrderHead k))

noncomputable def cutHeadHighInclusion : C.cutHeadHigh ⟶ C.cutA :=
  C.restrictFunctor.map (ModuleCat.ofHom ((S.highIdeal k 2).restrictScalars (S.PolynomialRing k)).subtype)
noncomputable def cutBProjection : C.cutA ⟶ C.cutB :=
  C.restrictFunctor.map (ModuleCat.ofHom (Ideal.Quotient.mkₐ (S.PolynomialRing k) (S.highIdeal k 2)).toLinearMap)

theorem cutHeadHigh_comp_B : C.cutHeadHighInclusion ≫ C.cutBProjection=0 := by
  ext a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property

noncomputable def cutBSequence : ShortComplex (ModuleCat (S.CutPolynomialRing k)) :=
  ShortComplex.mk C.cutHeadHighInclusion C.cutBProjection C.cutHeadHigh_comp_B

theorem cutBSequence_shortExact : C.cutBSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    exact ⟨⟨a,Ideal.Quotient.eq_zero_iff_mem.mp ha⟩,rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (Ideal.Quotient.mk (S.highIdeal k 2))
    exact Ideal.Quotient.mk_surjective

theorem cutB_finite : Module.Finite (S.CutPolynomialRing k) C.cutB := C.cut_finite (S.FirstOrderHead k)
theorem cutB_coefficientFinite : Module.Finite k (coefficientModule k (Fin S.actualCutRank) C.cutB) :=
  C.cut_coefficientFinite (S.FirstOrderHead k)
theorem cutHeadHigh_finite : Module.Finite (S.CutPolynomialRing k) C.cutHeadHigh :=
  C.cut_finite (S.highIdeal k 2)
theorem cutHeadHigh_coefficientFinite : Module.Finite k (coefficientModule k (Fin S.actualCutRank) C.cutHeadHigh) :=
  C.cut_coefficientFinite (S.highIdeal k 2)

noncomputable def cutBCoefficientEquiv : coefficientModule k (Fin S.actualCutRank) C.cutB ≃ₗ[k] S.FirstOrderHead k :=
  C.cutCoefficientEquiv (S.FirstOrderHead k)

theorem cutB_length : Module.finrank k (coefficientModule k (Fin S.actualCutRank) C.cutB)=S.embeddingDimension := by
  rw [C.cutBCoefficientEquiv.finrank_eq,S.firstOrderHead_finrank]

theorem cutB_X_mk (i : Fin S.actualCutRank) (a : S.HeadAlgebra k) :
    (MvPolynomial.X i : S.CutPolynomialRing k) •
      (show C.cutB from Ideal.Quotient.mk (S.highIdeal k 2) a)=
    (show C.cutB from Ideal.Quotient.mk (S.highIdeal k 2) ((C.forms i).val*a)) := by
  change Ideal.Quotient.mk (S.highIdeal k 2) (S.polynomialToA k (C.toPolynomialRing (MvPolynomial.X i)))*
      Ideal.Quotient.mk (S.highIdeal k 2) a=_
  rw [← map_mul,C.toPolynomialRing_X,C.polynomialForm_image]

noncomputable def cutBEuler (j : ℕ) : ℤ := by
  let := C.cutB_finite
  exact bettiEuler k (Fin S.actualCutRank) C.cutB j
noncomputable def cutHeadHighEuler (j : ℕ) : ℤ := by
  let := C.cutHeadHigh_finite
  exact bettiEuler k (Fin S.actualCutRank) C.cutHeadHigh j

theorem cutAEuler_le_high_B (j : ℕ) :
    letI := C.cutA_finite
    bettiEuler k (Fin S.actualCutRank) C.cutA j ≤ C.cutHeadHighEuler j+C.cutBEuler j := by
  let := C.cutB_finite
  let := C.cutHeadHigh_finite
  let : Module.Finite (S.CutPolynomialRing k) C.cutBSequence.X₁ := C.cutHeadHigh_finite
  let : Module.Finite (S.CutPolynomialRing k) C.cutBSequence.X₂ := C.cutA_finite
  let : Module.Finite (S.CutPolynomialRing k) C.cutBSequence.X₃ := C.cutB_finite
  have h := bettiEuler_middle_le k (Fin S.actualCutRank) C.cutBSequence C.cutBSequence_shortExact j
  exact h
end NSP14.NumericalSemigroup.LinearCutData
