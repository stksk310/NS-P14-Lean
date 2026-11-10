module
public import NSP14.Ordinary.CutResidualAction
public import NSP14.Homological.RegularRestriction
public import NSP14.Homological.FirstOrderBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutResidualModule : ModuleCat (VariableRing k (Fin C.complementRank)) :=
  polynomialRegularModule k (Fin C.complementRank)
    (S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank) C.complementPolynomialToResidual

noncomputable def cutResidualModelIso : C.cutResidualModule ≅ firstOrderModule k C.complementRank 0 := by
  let e : C.cutResidualModule ≃ₗ[VariableRing k (Fin C.complementRank)] firstOrderModule k C.complementRank 0 :=
    { toFun a := C.cutResidualEquiv (show S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank from a)
      invFun b := C.cutResidualEquiv.symm (show TrivSqZeroExt k (Fin C.complementRank → k) from b)
      left_inv a := C.cutResidualEquiv.symm_apply_apply a
      right_inv b := C.cutResidualEquiv.apply_symm_apply b
      map_add' a b := C.cutResidualEquiv.map_add a b
      map_smul' p a := by
        change C.cutResidualEquiv (C.complementPolynomialToResidual p*
          (show S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank from a))=
            firstOrderPolynomial k C.complementRank 0 p*C.cutResidualEquiv a
        rw [map_mul]
        have hp := AlgHom.congr_fun C.cutResidual_Z_action p
        change C.cutResidualEquiv (C.complementPolynomialToResidual p)=firstOrderPolynomial k C.complementRank 0 p at hp
        rw [hp] }
  exact e.toModuleIso

theorem cutResidual_finite : Module.Finite k (S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (S.linearCutIdeal k C.forms S.actualCutRank)).toLinearMap
    Ideal.Quotient.mk_surjective

theorem cutResidualModule_finite : Module.Finite (VariableRing k (Fin C.complementRank)) C.cutResidualModule := by
  let := C.cutResidual_finite
  unfold cutResidualModule
  infer_instance

theorem cutResidual_length : Module.finrank k (S.HeadAlgebra k ⧸ S.linearCutIdeal k C.forms S.actualCutRank)=1+C.complementRank := by
  rw [C.cutResidualEquiv.toLinearEquiv.finrank_eq]
  change Module.finrank k (k × (Fin C.complementRank → k))=_
  rw [Module.finrank_prod,Module.finrank_self,Module.finrank_pi]
  simp

theorem cutResidual_Z_betti_zero :
    letI := C.cutResidualModule_finite
    totalBetti k (Fin C.complementRank) C.cutResidualModule 0=1 := by
  let := C.cutResidualModule_finite
  rw [totalBetti_iso k (Fin C.complementRank) C.cutResidualModelIso,firstOrder_totalBetti_zero]

theorem cutResidual_Z_betti (i : ℕ) (hi : 1 ≤ i) :
    letI := C.cutResidualModule_finite
    totalBetti k (Fin C.complementRank) C.cutResidualModule i=i*(C.complementRank+1).choose (i+1) := by
  let := C.cutResidualModule_finite
  rw [totalBetti_iso k (Fin C.complementRank) C.cutResidualModelIso]
  exact firstOrder_ordinary_betti k C.complementRank i hi
end NSP14.NumericalSemigroup.LinearCutData
