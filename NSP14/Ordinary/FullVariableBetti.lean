module
public import NSP14.Ordinary.FullVariableChange
public import NSP14.Homological.RegularRestriction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def extendedFullG :
    ModuleCat (VariableRing k (Option (Fin (S.actualCutRank+C.complementRank)))) :=
  polynomialRegularModule k _ (S.TangentAlgebra k) C.extendedFullToG

noncomputable def extendedFullRestrictionIso :
    (ModuleCat.restrictScalars C.extendedFullPolynomialEquiv.toRingEquiv.toRingHom).obj
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) ≅ C.extendedFullG := by
  let e : (ModuleCat.restrictScalars C.extendedFullPolynomialEquiv.toRingEquiv.toRingHom).obj
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) ≃ₗ[VariableRing k (Option (Fin (S.actualCutRank+C.complementRank)))] C.extendedFullG :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

theorem extendedFullG_finite :
    Module.Finite (VariableRing k (Option (Fin (S.actualCutRank+C.complementRank)))) C.extendedFullG := by
  let := polynomialEquivRestricted_finite k _ _ C.extendedFullPolynomialEquiv
    (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k))
  exact Module.Finite.equiv C.extendedFullRestrictionIso.toLinearEquiv

/-- Ordinary Tor is preserved by the actual full polynomial change.
The ring has all e minimal variables, including the actual x. -/
theorem extendedFullG_totalBetti (i : ℕ) :
    letI := C.extendedFullG_finite
    totalBetti k (Option (Fin (S.actualCutRank+C.complementRank))) C.extendedFullG i=
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i := by
  let := C.extendedFullG_finite
  let := polynomialEquivRestricted_finite k _ _ C.extendedFullPolynomialEquiv
    (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k))
  calc
    _ = totalBetti k (Option (Fin (S.actualCutRank+C.complementRank)))
        ((ModuleCat.restrictScalars C.extendedFullPolynomialEquiv.toRingEquiv.toRingHom).obj
          (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k))) i :=
      (totalBetti_iso k _ C.extendedFullRestrictionIso i).symm
    _ = _ := polynomialEquiv_totalBetti k _ _ C.extendedFullPolynomialEquiv
      C.extendedFullPolynomialEquiv_augmentation _ i
end NSP14.NumericalSemigroup.LinearCutData
