module
public import NSP14.Homological.TwoStepBetti
public import NSP14.Homological.SquareZeroModel
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14.Homological
namespace TwoStepActualAcceptance
abbrev k := ZMod 2
noncomputable abbrev M := firstOrderModule k 1 0

noncomputable def scalarOne : k ≃ₗ[k] (Fin 1 → k) where
  toFun c _ := c
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by funext i;have h : i=0 := Subsingleton.elim _ _;subst i;rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def coords : coefficientModule k (Fin 1) M ≃ₗ[k] ((Fin 1 → k) × (Fin 1 → k)) :=
  (firstOrderCoefficientEquiv k 1 0).trans
    (LinearEquiv.prodCongr scalarOne (LinearEquiv.refl k (Fin 1 → k)))

def points (_ : Fin 1) : k := 0

theorem points_injective : Function.Injective points := fun _ _ _ => Subsingleton.elim _ _

theorem actual_action (v : Fin 1) (a : coefficientModule k (Fin 1) M) :
    coords ((MvPolynomial.X v : VariableRing k (Fin 1)) • a)=
      (0,momentFunctional k 1 (points v) (coords a).1 • (fun i : Fin 1 => points v^i.val)) := by
  have hv : v=0 := Subsingleton.elim _ _
  subst v
  apply Prod.ext
  · funext i
    change (firstOrderCoefficientEquiv k 1 0 ((MvPolynomial.X 0 : VariableRing k (Fin 1)) • a)).fst=0
    rw [firstOrder_variable]
    simp
  · funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    change (firstOrderCoefficientEquiv k 1 0 ((MvPolynomial.X 0 : VariableRing k (Fin 1)) • a)).snd 0=_
    rw [firstOrder_variable]
    simp [momentFunctional,Fintype.linearCombination_apply,coords,scalarOne,points,
      TrivSqZeroExt.snd_mul,op_smul_eq_smul]
    rfl

/-- The new rank calculation is applied to an actual polynomial module,
with a nonzero boundary, rather than only a separately defined matrix. -/
theorem actual_betti (i : ℕ) : totalBetti k (Fin 1) M i=if i=0 ∨ i=1 then 1 else 0 := by
  rw [twoStep_betti k (Fin 1) M 1 1 coords points actual_action points_injective (by decide) (by decide)]
  cases i with
  | zero => decide
  | succ i => cases i with
    | zero => decide
    | succ i =>
      simp
      exact Nat.choose_eq_zero_of_lt (by omega)
end TwoStepActualAcceptance
