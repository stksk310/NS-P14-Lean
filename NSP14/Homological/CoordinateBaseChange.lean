module

public import NSP14.Homological.PolynomialLinearMaps
public import NSP14.Homological.KoszulPolynomialBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ I : Type u) [Field k] [Field L] [Algebra k L]
variable (M : ModuleCat.{u} (VariableRing k σ)) (N : ModuleCat.{u} (VariableRing L σ))
variable (c : coefficientModule k σ M ≃ₗ[k] (I →₀ k))
variable (d : coefficientModule L σ N ≃ₗ[L] (I →₀ L))

noncomputable def coordinateBasis : Module.Basis I k (coefficientModule k σ M) :=
  Finsupp.basisSingleOne.map c.symm

noncomputable def coordinateBaseChangeEquiv :
    (L ⊗[k] coefficientModule k σ M) ≃ₗ[L] coefficientModule L σ N :=
  ((coordinateBasis k σ I M c).baseChange L).repr.trans d.symm

theorem coordinateBaseChangeEquiv_tmul (l : L) (m : coefficientModule k σ M) (i : I) :
    d (coordinateBaseChangeEquiv k L σ I M N c d (l ⊗ₜ[k] m)) i=
      algebraMap k L (c m i) * l := by
  classical
  simp [coordinateBaseChangeEquiv,Module.Basis.baseChange_repr_tmul,
    coordinateBasis,Module.Basis.map_repr,Algebra.smul_def]

/-- Polynomial-linearity is checked on the true variable matrices in the given bases. -/
noncomputable def coordinateBaseChangePolynomialIso
    (hm : ∀ (x : σ) (i j : I),
      d ((MvPolynomial.X x : VariableRing L σ) • d.symm (Finsupp.single i 1)) j=
        algebraMap k L (c ((MvPolynomial.X x : VariableRing k σ) • c.symm (Finsupp.single i 1)) j)) :
    polynomialBaseChangeModule k L σ M ≅ N := by
  classical
  let e := (polynomialBaseChangeCoefficientIso k L σ M).toLinearEquiv.trans
    (coordinateBaseChangeEquiv k L σ I M N c d)
  have hx : ∀ (x : σ) a,e ((MvPolynomial.X x : VariableRing L σ) • a)=
      (MvPolynomial.X x : VariableRing L σ) • e a := by
    intro x
    let f : (L ⊗[k] coefficientModule k σ M) →ₗ[L] coefficientModule L σ N :=
      (coordinateBaseChangeEquiv k L σ I M N c d).toLinearMap.comp
        (extendedPolynomialRepresentation k L σ M (MvPolynomial.X x))
    let g : (L ⊗[k] coefficientModule k σ M) →ₗ[L] coefficientModule L σ N :=
      (coefficientMap L σ (ModuleCat.ofHom (X := N) (Y := N) (variableOperator L σ N x))).comp
        (coordinateBaseChangeEquiv k L σ I M N c d).toLinearMap
    have he : f=g := by
      apply ((coordinateBasis k σ I M c).baseChange L).ext
      intro i
      apply d.injective
      ext j
      rw [Module.Basis.baseChange_apply]
      change d (coordinateBaseChangeEquiv k L σ I M N c d
        (extendedPolynomialRepresentation k L σ M (MvPolynomial.X x)
          (1 ⊗ₜ[k] (coordinateBasis k σ I M c i)))) j = _
      rw [polynomialBaseChange_variable,coordinateBaseChangeEquiv_tmul,mul_one]
      have hb : coordinateBaseChangeEquiv k L σ I M N c d
          (1 ⊗ₜ[k] coordinateBasis k σ I M c i)=d.symm (Finsupp.single i 1) := by
        apply d.injective
        ext j
        rw [coordinateBaseChangeEquiv_tmul,LinearEquiv.apply_symm_apply]
        by_cases hij : i=j <;> simp [coordinateBasis,hij]
      change _=d ((MvPolynomial.X x : VariableRing L σ) •
        coordinateBaseChangeEquiv k L σ I M N c d (1 ⊗ₜ[k] coordinateBasis k σ I M c i)) j
      rw [hb,hm]
      rfl
    intro a
    exact LinearMap.congr_fun he a
  let f := polynomialHomOfVariables L σ e.toLinearMap hx
  have hf : Function.Bijective f := e.bijective
  exact (LinearEquiv.ofBijective f.hom hf).toModuleIso

end NSP14.Homological
