module
public import NSP14.Endpoint.TwoActionTop
public import NSP14.Homological.RegularActionCoefficient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint
variable (k A : Type) [Field k] [CommRing A] [Algebra k A] (r s : A)

noncomputable def twoScalarSocle : Submodule k A :=
  ((LinearMap.mul k A).flip r).ker⊓((LinearMap.mul k A).flip s).ker

noncomputable def twoNativeSocle : Submodule A A :=
  (r • 𝟙 (ModuleCat.of A A)).hom.ker⊓(s • 𝟙 (ModuleCat.of A A)).hom.ker

noncomputable def twoNativeSocleCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj (ModuleCat.of A (twoNativeSocle A r s))

noncomputable def twoSocleCoefficientEquiv : twoNativeSocleCoefficients k A r s ≃ₗ[k] twoScalarSocle k A r s where
  toFun a := ⟨a.val,by
    have h0 : r*a.val=0 := a.property.1
    have h1 : s*a.val=0 := a.property.2
    exact ⟨by change a.val*r=0;rw [mul_comm];exact h0,
      by change a.val*s=0;rw [mul_comm];exact h1⟩⟩
  invFun a := ⟨a.val,by
    have h0 : a.val*r=0 := a.property.1
    have h1 : a.val*s=0 := a.property.2
    exact ⟨by change r*a.val=0;rw [mul_comm];exact h0,
      by change s*a.val=0;rw [mul_comm];exact h1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    apply Subtype.ext
    change (algebraMap k A c)*a.val=c • a.val
    exact (Algebra.smul_def c a.val).symm

noncomputable def twoScalarH2Equiv :
    (regularPartialCoefficientComplex k A [s,r]).homology 2 ≃ₗ[k] twoScalarSocle k A r s :=
  (nativeCoefficientHomologyIso k A (actionRegularComplex A [s,r]) 2).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k A)).mapIso
      (twoActionH2Equiv A r s (ModuleCat.of A A)).toModuleIso).toLinearEquiv.trans
        (twoSocleCoefficientEquiv k A r s))
end NSP14.Endpoint
