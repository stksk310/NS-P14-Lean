module
public import NSP14.Homological.KoszulGrading
public import NSP14.Homological.RegularRestriction
public import NSP14.Homological.PolynomialEquivBetti
public import Mathlib.Algebra.MvPolynomial.Rename
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Homological
variable (k τ σ : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    (φ : MvPolynomial σ k →ₐ[k] A) (e : τ ≃ σ)

def relabeledRegularMap : MvPolynomial τ k →ₐ[k] A := φ.comp (MvPolynomial.renameEquiv k e).toAlgHom

variable (G : GradedPolynomialModule k σ (polynomialRegularModule k σ A φ))

def relabeledRegularGrading : GradedPolynomialModule k τ (polynomialRegularModule k τ A (relabeledRegularMap k τ σ A φ e)) where
  piece := G.piece
  inclusion n := (regularRestrictionCoefficientEquiv k τ A (relabeledRegularMap k τ σ A φ e)).symm.toLinearMap.comp
    ((regularRestrictionCoefficientEquiv k σ A φ).toLinearMap.comp (G.inclusion n))
  sum_bijective := by
    let c := (regularRestrictionCoefficientEquiv k σ A φ).trans
      (regularRestrictionCoefficientEquiv k τ A (relabeledRegularMap k τ σ A φ e)).symm
    have he : DirectSum.toModule k ℤ _ (fun n => c.toLinearMap.comp (G.inclusion n))=
        c.toLinearMap.comp (DirectSum.toModule k ℤ _ G.inclusion) := by
      apply DirectSum.linearMap_ext
      intro n
      ext a
      simp only [LinearMap.comp_apply,DirectSum.toModule_lof]
    change Function.Bijective (DirectSum.toModule k ℤ _ (fun n => c.toLinearMap.comp (G.inclusion n)))
    rw [he]
    exact c.bijective.comp G.sum_bijective
  variableMap x := G.variableMap (e x)
  variable_commutes x n a := by
    apply (regularRestrictionCoefficientEquiv k τ A (relabeledRegularMap k τ σ A φ e)).injective
    change (regularRestrictionCoefficientEquiv k σ A φ) (G.inclusion (n+1) (G.variableMap (e x) n a))=
      relabeledRegularMap k τ σ A φ e (MvPolynomial.X x)*
        (regularRestrictionCoefficientEquiv k σ A φ) (G.inclusion n a)
    rw [G.variable_commutes]
    change φ (MvPolynomial.X (e x))*_ = φ ((MvPolynomial.renameEquiv k e) (MvPolynomial.X x))*_
    rw [MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
    rfl

theorem relabeledRegularGrading_unit
    (hu : (regularRestrictionCoefficientEquiv k σ A φ).symm 1∈G.degreeSpace 0) :
    (regularRestrictionCoefficientEquiv k τ A (relabeledRegularMap k τ σ A φ e)).symm 1∈
      (relabeledRegularGrading k τ σ A φ e G).degreeSpace 0 := by
  obtain ⟨a,ha⟩ := hu
  refine ⟨a,?_⟩
  change (regularRestrictionCoefficientEquiv k τ A (relabeledRegularMap k τ σ A φ e)).symm
    ((regularRestrictionCoefficientEquiv k σ A φ) (G.inclusion 0 a))=_
  rw [ha,LinearEquiv.apply_symm_apply]

theorem renameEquiv_augmentation :
    (augmentation k σ).comp (MvPolynomial.renameEquiv k e).toAlgHom=augmentation k τ := by
  apply MvPolynomial.algHom_ext
  intro i
  change augmentation k σ ((MvPolynomial.renameEquiv k e) (MvPolynomial.X i))=augmentation k τ (MvPolynomial.X i)
  rw [MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,augmentation_X,augmentation_X]

theorem relabeledRegular_totalBetti [Fintype τ] [Fintype σ] [Module.Finite k A] (i : ℕ) :
    totalBetti k τ (polynomialRegularModule k τ A (relabeledRegularMap k τ σ A φ e)) i=
      totalBetti k σ (polynomialRegularModule k σ A φ) i := by
  exact polynomialEquiv_totalBetti k τ σ (MvPolynomial.renameEquiv k e) (renameEquiv_augmentation k τ σ e)
    (polynomialRegularModule k σ A φ) i
end NSP14.Homological

