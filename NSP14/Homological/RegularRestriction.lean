module
public import NSP14.Homological.RestrictedScalars
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]
  (A : Type u) [CommRing A] [Algebra k A]

noncomputable def polynomialRegularModule (φ : VariableRing k σ →ₐ[k] A) : ModuleCat.{u} (VariableRing k σ) :=
  (ModuleCat.restrictScalars φ.toRingHom).obj (ModuleCat.of A A)

noncomputable def regularRestrictionCoefficientEquiv (φ : VariableRing k σ →ₐ[k] A) :
    coefficientModule k σ (polynomialRegularModule k σ A φ) ≃ₗ[k] A where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change φ (algebraMap k (VariableRing k σ) c)*(show A from a)=c • (show A from a)
    rw [φ.commutes,Algebra.smul_def]

noncomputable instance regularRestriction_coefficientFinite (φ : VariableRing k σ →ₐ[k] A) [Module.Finite k A] :
    Module.Finite k (coefficientModule k σ (polynomialRegularModule k σ A φ)) :=
  Module.Finite.equiv (regularRestrictionCoefficientEquiv k σ A φ).symm

noncomputable instance regularRestriction_finite (φ : VariableRing k σ →ₐ[k] A) [Module.Finite k A] :
    Module.Finite (VariableRing k σ) (polynomialRegularModule k σ A φ) :=
  polynomialFinite_of_coefficientFinite _

variable (B : Type u) [CommRing B] [Algebra k B]

/-- An algebra equivalence intertwining the actual polynomial maps gives
an actual module isomorphism over that polynomial ring. -/
noncomputable def polynomialRegularModuleIso
    (φ : VariableRing k σ →ₐ[k] A) (ψ : VariableRing k σ →ₐ[k] B) (e : A ≃ₐ[k] B)
    (h : e.toAlgHom.comp φ=ψ) : polynomialRegularModule k σ A φ ≅ polynomialRegularModule k σ B ψ := by
  let l : polynomialRegularModule k σ A φ ≃ₗ[VariableRing k σ] polynomialRegularModule k σ B ψ :=
    { toFun a := e (show A from a)
      invFun b := e.symm (show B from b)
      left_inv a := e.symm_apply_apply a
      right_inv b := e.apply_symm_apply b
      map_add' a b := e.map_add a b
      map_smul' p a := by
        change e (φ p*(show A from a))=ψ p*e (show A from a)
        rw [map_mul]
        have hp := AlgHom.congr_fun h p
        change e (φ p)=ψ p at hp
        rw [hp] }
  exact l.toModuleIso
end NSP14.Homological
