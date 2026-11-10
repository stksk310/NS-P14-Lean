module
public import NSP14.Homological.HankelEvaluation
public import NSP14.Homological.LinearCoefficientAction
public import NSP14.Homological.EvaluationVariables
public import NSP14.Homological.TwoStepBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type) [Field k] (r : ℕ) (M : ModuleCat (VariableRing k (Fin r)))
  [Module.Finite (VariableRing k (Fin r)) M]
  (d n : ℕ) (e : coefficientModule k (Fin r) M ≃ₗ[k] ((Fin d → k) × (Fin n → k)))
  (points : Fin r → k) (hp : Function.Injective points)

noncomputable abbrev hankelVariableEquiv := evaluationVariableEquiv k (Fin r) r (Equiv.refl _) points hp

noncomputable abbrev hankelChangedModule : ModuleCat (VariableRing k (Fin r)) :=
  (ModuleCat.restrictScalars (polynomialLinearEquiv (hankelVariableEquiv k r points hp)).toRingEquiv.toRingHom).obj M

noncomputable def hankelOriginalCoefficientEquiv :
    coefficientModule k (Fin r) (hankelChangedModule k r M points hp) ≃ₗ[k]
      coefficientModule k (Fin r) M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change polynomialLinearEquiv (hankelVariableEquiv k r points hp)
      (algebraMap k (VariableRing k (Fin r)) c) • (show M from a)=
        algebraMap k (VariableRing k (Fin r)) c • (show M from a)
    rw [(polynomialLinearEquiv (hankelVariableEquiv k r points hp)).commutes]

noncomputable def hankelChangedCoordinates :
    coefficientModule k (Fin r) (hankelChangedModule k r M points hp) ≃ₗ[k]
      ((Fin d → k) × (Fin n → k)) :=
  (hankelOriginalCoefficientEquiv k r M points hp).trans e

variable (hcard : d+n=r+1)
  (hHankel : ∀ j (a : coefficientModule k (Fin r) M),
    e ((MvPolynomial.X j : VariableRing k (Fin r)) • a)=hankelAction k d n j.val (e a))

omit [Module.Finite (VariableRing k (Fin r)) M] in
include hcard hHankel in
theorem hankelChanged_action (j : Fin r)
    (a : coefficientModule k (Fin r) (hankelChangedModule k r M points hp)) :
    hankelChangedCoordinates k r M d n e points hp ((MvPolynomial.X j : VariableRing k (Fin r)) • a)=
      (0,momentFunctional k d (points j) (hankelChangedCoordinates k r M d n e points hp a).1 •
        (fun i : Fin n => points j^i.val)) := by
  let F := hankelOriginalCoefficientEquiv k r M points hp
  change e (F ((MvPolynomial.X j : VariableRing k (Fin r)) • a))=_
  have ha : F ((MvPolynomial.X j : VariableRing k (Fin r)) • a)=
      polynomialLinearEquiv (hankelVariableEquiv k r points hp) (MvPolynomial.X j) • F a := rfl
  rw [ha]
  change e (linearSubstitution (hankelVariableEquiv k r points hp).toLinearMap (MvPolynomial.X j) • F a)=_
  rw [linearSubstitution_X,linearPolynomial_coefficient_smul,map_sum]
  simp only [map_smul,hHankel]
  have hc := evaluationVariableEquiv_single k (Fin r) r (Equiv.refl _) points hp j
  simp only [hankelVariableEquiv,LinearEquiv.coe_coe]
  simp_rw [hc]
  exact hankel_evaluation k d n r hcard (points j) (e (F a))

include hcard hHankel hp in
/-- All-row actual Tor formula for a Hankel module, obtained through a
real invertible polynomial variable change. -/
theorem hankelModule_betti (hd : 1 ≤ d) (i : ℕ) :
    totalBetti k (Fin r) M i=
      if i+1≤d then (d-i)*(r+1).choose i else (i+1-d)*(r+1).choose (i+1) := by
  let := polynomialEquivRestricted_finite k (Fin r) (Fin r)
    (polynomialLinearEquiv (hankelVariableEquiv k r points hp)) M
  have hb := twoStep_betti k (Fin r) (hankelChangedModule k r M points hp) d n
    (hankelChangedCoordinates k r M d n e points hp) points
    (hankelChanged_action k r M d n e points hp hcard hHankel) hp hd (by simpa using hcard) i
  change totalBetti k (Fin r) ((ModuleCat.restrictScalars
    (polynomialLinearEquiv (hankelVariableEquiv k r points hp)).toRingEquiv.toRingHom).obj M) i=_ at hb
  rw [polynomialLinearEquiv_totalBetti k (Fin r) (Fin r) (hankelVariableEquiv k r points hp) M i] at hb
  simpa only [Fintype.card_fin] using hb
end NSP14.Homological
