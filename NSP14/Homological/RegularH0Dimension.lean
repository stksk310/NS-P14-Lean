module
public import NSP14.Homological.RegularActionCoefficient
public import NSP14.Homological.SquareZeroModel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

noncomputable def regularPartialH0CoefficientIso (f : ℕ) (rs : List R) (φ : VariableRing k (Fin f) →ₐ[k] R) :
    (regularPartialCoefficientComplex k R rs).homology 0 ≅
      coefficientModule k (Fin f) (actionRestrictedH0 rs φ.toRingHom) :=
  nativeCoefficientHomologyIso k R (actionRegularComplex R rs) 0 ≪≫
    (algebraRestrictionCoefficientEquiv k (VariableRing k (Fin f)) R φ _).toModuleIso.symm

theorem regularPartialH0_squareZero_length (f : ℕ) (rs : List R) (φ : VariableRing k (Fin f) →ₐ[k] R)
    (e : actionRestrictedH0 rs φ.toRingHom ≅ firstOrderModule k f 0) :
    Module.finrank k ((regularPartialCoefficientComplex k R rs).homology 0)=1+f := by
  have h := (regularPartialH0CoefficientIso k R f rs φ).toLinearEquiv.finrank_eq
  have he := ((ModuleCat.restrictScalars (algebraMap k (VariableRing k (Fin f)))).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank k (coefficientModule k (Fin f) (actionRestrictedH0 rs φ.toRingHom))=
    Module.finrank k (coefficientModule k (Fin f) (firstOrderModule k f 0)) at he
  exact h.trans (he.trans (by simpa only [Nat.add_zero] using firstOrder_length k f 0))
end NSP14.Homological
