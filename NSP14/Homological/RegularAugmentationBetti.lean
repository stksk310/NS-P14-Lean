module
public import NSP14.Homological.ZerothBettiEpi
public import NSP14.Homological.RegularRestriction
public import NSP14.Homological.KoszulFree
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ A : Type u) [Field k] [Fintype σ] [CommRing A] [Algebra k A]

noncomputable def regularPresentationMorphism (φ : VariableRing k σ →ₐ[k] A) :
    ModuleCat.of (VariableRing k σ) (VariableRing k σ) ⟶ polynomialRegularModule k σ A φ :=
  ModuleCat.ofHom (X:=ModuleCat.of (VariableRing k σ) (VariableRing k σ))
    (Y:=polynomialRegularModule k σ A φ)
    { toFun p := φ p
      map_add' := φ.map_add
      map_smul' := φ.map_mul }

omit [Fintype σ] in
theorem regularPresentation_finite (φ : VariableRing k σ →ₐ[k] A) (hφ : Function.Surjective φ) :
    Module.Finite (VariableRing k σ) (polynomialRegularModule k σ A φ) :=
  Module.Finite.of_surjective (regularPresentationMorphism k σ A φ).hom hφ

noncomputable def regularAugmentationMorphism (φ : VariableRing k σ →ₐ[k] A) (ψ : A →ₐ[k] k)
    (hψ : ψ.comp φ=augmentation k σ) : polynomialRegularModule k σ A φ ⟶ residueField k σ :=
  ModuleCat.ofHom (X:=polynomialRegularModule k σ A φ) (Y:=residueField k σ)
    { toFun a := ψ (show A from a)
      map_add' a b := ψ.map_add a b
      map_smul' p a := by
        change ψ (φ p*(show A from a))=augmentation k σ p*ψ (show A from a)
        rw [map_mul]
        have h := AlgHom.congr_fun hψ p
        change ψ (φ p)=augmentation k σ p at h
        rw [h] }

omit [Fintype σ] in
theorem residueField_finite : Module.Finite (VariableRing k σ) (residueField k σ) := by
  apply Module.Finite.of_surjective (augmentationLinear k σ)
  intro c
  exact ⟨MvPolynomial.C (show k from c),(augmentation k σ).commutes c⟩

/-- A genuine cyclic augmented presentation has actual zeroth Betti one.
Finiteness is supplied by the real surjective polynomial presentation. -/
theorem regularAugmented_totalBetti_zero (φ : VariableRing k σ →ₐ[k] A) (ψ : A →ₐ[k] k)
    (hφ : Function.Surjective φ) (hψ : ψ.comp φ=augmentation k σ) :
    letI := regularPresentation_finite k σ A φ hφ
    totalBetti k σ (polynomialRegularModule k σ A φ) 0=1 := by
  let := regularPresentation_finite k σ A φ hφ
  let := residueField_finite k σ
  let : Epi (regularPresentationMorphism k σ A φ) := (ModuleCat.epi_iff_surjective _).mpr hφ
  let : Epi (regularAugmentationMorphism k σ A φ ψ hψ) := by
    rw [ModuleCat.epi_iff_surjective]
    intro c
    exact ⟨algebraMap k A (show k from c),ψ.commutes c⟩
  have hu := totalBetti_zero_le_of_epi k σ (regularPresentationMorphism k σ A φ)
  have hl := totalBetti_zero_le_of_epi k σ (regularAugmentationMorphism k σ A φ ψ hψ)
  rw [totalBetti_free_zero] at hu
  rw [residueField_totalBetti_zero] at hl
  omega
end NSP14.Homological
