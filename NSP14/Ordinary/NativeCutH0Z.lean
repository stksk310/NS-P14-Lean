module
public import NSP14.Ordinary.NativeCutH0
public import NSP14.Homological.ActionH0Image
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def extendedPolynomialToG :
    MvPolynomial (Fin (S.actualCutRank+C.complementRank)) k →ₐ[k] S.TangentAlgebra k :=
  (S.polynomialToG k).comp C.extendedPolynomialEquiv.toAlgHom

noncomputable def complementPolynomialToG :
    MvPolynomial (Fin C.complementRank) k →ₐ[k] S.TangentAlgebra k :=
  C.extendedPolynomialToG.comp (MvPolynomial.rename (Fin.natAdd S.actualCutRank))

theorem complementPolynomialToG_head : (S.toHeadAlgebra k).comp C.complementPolynomialToG=C.complementPolynomialToA := rfl

theorem nativeToResidual_Z_action :
    C.nativeToResidual.comp C.complementPolynomialToG=firstOrderPolynomial k C.complementRank 0 := by
  change C.headToResidual.comp ((S.toHeadAlgebra k).comp C.complementPolynomialToG)=_
  rw [C.complementPolynomialToG_head,C.headToResidual_Z_action]

/-- Native R-Koszul H0, with the actual complementary Z action inherited
from the G-linear complex. The action is not chosen by transporting dimensions. -/
noncomputable abbrev nativeCutH0Z : ModuleCat (VariableRing k (Fin C.complementRank)) :=
  actionRestrictedH0 C.nativeCutVariables C.complementPolynomialToG.toRingHom

/-- The actual induced action on H0 is the ordinary square-zero Z model. -/
noncomputable def nativeCutH0ZIso : C.nativeCutH0Z ≅ firstOrderModule k C.complementRank 0 :=
  actionRestrictedH0Iso C.nativeCutVariables C.nativeToResidual.toRingHom
    C.nativeToResidual_surjective C.nativeToResidual_ker C.complementPolynomialToG.toRingHom
    (firstOrderPolynomial k C.complementRank 0).toRingHom
    (by apply RingHom.ext;intro p;exact (AlgHom.congr_fun C.nativeToResidual_Z_action p).symm)

theorem nativeCutH0Z_finite : Module.Finite (VariableRing k (Fin C.complementRank)) C.nativeCutH0Z :=
  Module.Finite.equiv C.nativeCutH0ZIso.symm.toLinearEquiv

theorem nativeCutH0Z_betti_zero :
    letI := C.nativeCutH0Z_finite
    totalBetti k (Fin C.complementRank) C.nativeCutH0Z 0=1 := by
  let := C.nativeCutH0Z_finite
  rw [totalBetti_iso k (Fin C.complementRank) C.nativeCutH0ZIso,firstOrder_totalBetti_zero]

theorem nativeCutH0Z_betti (i : ℕ) (hi : 1 ≤ i) :
    letI := C.nativeCutH0Z_finite
    totalBetti k (Fin C.complementRank) C.nativeCutH0Z i=i*(C.complementRank+1).choose (i+1) := by
  let := C.nativeCutH0Z_finite
  rw [totalBetti_iso k (Fin C.complementRank) C.nativeCutH0ZIso]
  exact firstOrder_ordinary_betti k C.complementRank i hi
end NSP14.NumericalSemigroup.LinearCutData
