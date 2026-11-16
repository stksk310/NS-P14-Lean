module
public import NSP14.Homological.LinearVariableBetti
public import NSP14.Homological.SquareZeroModel
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
@[expose] public section
open CategoryTheory NSP14.Homological
namespace LinearVariableBettiAcceptance
variable (k : Type) [Field k]

noncomputable def shear : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) where
  toFun v i := if i=0 then v 0+v 1 else v 1
  invFun v i := if i=0 then v 0-v 1 else v 1
  left_inv v := by funext i;fin_cases i <;> simp
  right_inv v := by funext i;fin_cases i <;> simp
  map_add' v w := by funext i;fin_cases i <;> simp;ring
  map_smul' c v := by funext i;fin_cases i <;> simp [smul_eq_mul];ring

theorem mixed_variable : polynomialLinearEquiv (shear k) (MvPolynomial.X (1 : Fin 2))=
    MvPolynomial.X (0 : Fin 2)+MvPolynomial.X (1 : Fin 2) := by
  change linearSubstitution (shear k).toLinearMap (MvPolynomial.X (1 : Fin 2))=_
  rw [linearSubstitution_X,linearPolynomial_apply,Fin.sum_univ_two]
  simp [shear]

theorem ordinary_Tor_variable_change (M : ModuleCat (VariableRing k (Fin 2)))
    [Module.Finite (VariableRing k (Fin 2)) M] (i : ℕ) :
    letI := polynomialEquivRestricted_finite k _ _ (polynomialLinearEquiv (shear k)) M
    totalBetti k (Fin 2) ((ModuleCat.restrictScalars (polynomialLinearEquiv (shear k)).toRingEquiv.toRingHom).obj M) i=
      totalBetti k (Fin 2) M i := polynomialLinearEquiv_totalBetti k _ _ (shear k) M i

theorem characteristic_two_all_rows (i : ℕ) :
    letI := polynomialEquivRestricted_finite (ZMod 2) _ _ (polynomialLinearEquiv (shear (ZMod 2)))
      (firstOrderModule (ZMod 2) 2 0)
    totalBetti (ZMod 2) (Fin 2)
      ((ModuleCat.restrictScalars (polynomialLinearEquiv (shear (ZMod 2))).toRingEquiv.toRingHom).obj
        (firstOrderModule (ZMod 2) 2 0)) i=totalBetti (ZMod 2) (Fin 2) (firstOrderModule (ZMod 2) 2 0) i :=
  ordinary_Tor_variable_change (ZMod 2) _ i
end LinearVariableBettiAcceptance
