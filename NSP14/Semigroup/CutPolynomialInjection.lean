module
public import NSP14.Semigroup.CutAction
public import NSP14.Homological.PolynomialInjection
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

theorem linearFormPolynomial_eq (v : S.NonXAtom → k) :
    S.linearFormPolynomial k v=NSP14.Homological.linearPolynomial k S.NonXAtom v := by
  unfold linearFormPolynomial NSP14.Homological.linearPolynomial
  change (∑ x, MvPolynomial.C (v x)*MvPolynomial.X x)=∑ x,v x • MvPolynomial.X x
  apply Finset.sum_congr rfl
  intro x _
  exact (Algebra.smul_def _ _).symm

namespace LinearCutData
variable {S k} (C : S.LinearCutData k)

noncomputable def coefficientInjection : (Fin S.actualCutRank → k) →ₗ[k] (S.NonXAtom → k) :=
  Fintype.linearCombination k (fun i => S.headLinearCoordinates k (C.forms i))

theorem coefficientInjection_injective : Function.Injective C.coefficientInjection := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mp
  exact C.independent.map' (S.headLinearCoordinates k).toLinearMap
    (LinearEquiv.ker (S.headLinearCoordinates k))

theorem toPolynomialRing_eq_linearSubstitution :
    C.toPolynomialRing=NSP14.Homological.linearSubstitution C.coefficientInjection := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [C.toPolynomialRing_X,NSP14.Homological.linearSubstitution_X]
  unfold coefficientInjection
  rw [Fintype.linearCombination_apply_single]
  simp only [one_smul]
  exact S.linearFormPolynomial_eq k _

/-- P embeds in the non-x polynomial ring; no independence of its images
inside the Artin quotient A is asserted. -/
theorem toPolynomialRing_injective : Function.Injective C.toPolynomialRing := by
  rw [C.toPolynomialRing_eq_linearSubstitution]
  exact NSP14.Homological.linearSubstitution_injective _ C.coefficientInjection_injective
end LinearCutData
end NSP14.NumericalSemigroup
