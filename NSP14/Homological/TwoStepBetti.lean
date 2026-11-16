module
public import NSP14.Homological.TwoStepBoundary
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
  (d n : ℕ) (e : coefficientModule k σ M ≃ₗ[k] ((Fin d → k) × (Fin n → k))) (points : σ → k)
  (hact : ∀ v (a : coefficientModule k σ M),
    e ((MvPolynomial.X v : VariableRing k σ) • a)=
      (0,momentFunctional k d (points v) (e a).1 • (fun i : Fin n => points v^i.val)))

omit [Module.Finite (VariableRing k σ) M] [Fintype σ] in
include e in
theorem twoStep_coefficientFinite : Module.Finite k (coefficientModule k σ M) :=
  Module.Finite.equiv e.symm

omit [Module.Finite (VariableRing k σ) M] [Fintype σ] in
include e in
theorem twoStep_length : Module.finrank k (coefficientModule k σ M)=d+n := by
  rw [e.finrank_eq,Module.finrank_prod]
  simp

omit [Module.Finite (VariableRing k σ) M] in
include hact in
theorem twoStep_boundary_above (hp : Function.Injective points) (j : ℕ)
    (hrow : Fintype.card σ-j ≤ n) (hcol : d ≤ j+1) :
    koszulBoundaryRank k σ M (j+1)=d*(Fintype.card σ).choose (j+1) := by
  have h := twoStepBoundary_rank_above k σ M d n e points hact hp j hrow hcol
  rw [coefficientKoszulListFunctor_full,coefficientKoszulFunctor_obj] at h
  simpa only [koszulBoundaryRank,chainBoundaryRank_succ] using h

omit [Module.Finite (VariableRing k σ) M] in
include hact in
theorem twoStep_boundary_below (hp : Function.Injective points) (j : ℕ)
    (hrow : n ≤ Fintype.card σ-j) (hcol : j+1 ≤ d) :
    koszulBoundaryRank k σ M (j+1)=n*(Fintype.card σ).choose j := by
  have h := twoStepBoundary_rank_below k σ M d n e points hact hp j hrow hcol
  rw [coefficientKoszulListFunctor_full,coefficientKoszulFunctor_obj] at h
  simpa only [koszulBoundaryRank,chainBoundaryRank_succ] using h

include hact in
theorem twoStep_betti_zero (hp : Function.Injective points) (hd : 1 ≤ d)
    (hcard : d+n=Fintype.card σ+1) : totalBetti k σ M 0=d := by
  let := twoStep_coefficientFinite k σ M d n e
  have he := koszul_betti_chain_rank k σ M 0
  rw [koszulBoundaryRank,chainBoundaryRank_zero] at he
  rw [twoStep_boundary_below k σ M d n e points hact hp 0 (by omega) hd,
    twoStep_length k σ M d n e] at he
  simp only [Nat.choose_zero_right,Nat.mul_one,Nat.add_zero] at he
  omega

include hact in
/-- Actual all-row Betti calculation for a two-step module whose real
variable actions have the indicated evaluation form. -/
theorem twoStep_betti (hp : Function.Injective points) (hd : 1 ≤ d)
    (hcard : d+n=Fintype.card σ+1) (i : ℕ) :
    totalBetti k σ M i=
      if i+1≤d then (d-i)*(Fintype.card σ+1).choose i
      else (i+1-d)*(Fintype.card σ+1).choose (i+1) := by
  let := twoStep_coefficientFinite k σ M d n e
  cases i with
  | zero =>
    rw [twoStep_betti_zero k σ M d n e points hact hp hd hcard]
    simp [hd]
  | succ j =>
    have he := koszul_betti_chain_rank k σ M (j+1)
    rw [twoStep_length k σ M d n e] at he
    by_cases hi : j+1+1 ≤ d
    · rw [ite_eq_left hi]
      rw [twoStep_boundary_below k σ M d n e points hact hp j (by omega) (by omega),
        twoStep_boundary_below k σ M d n e points hact hp (j+1) (by omega) hi] at he
      have hw := Nat.add_one_mul_choose_eq (Fintype.card σ) j
      rw [← hcard] at hw
      have hP := Nat.choose_succ_succ (Fintype.card σ) j
      change (Fintype.card σ+1).choose (j+1)=
        (Fintype.card σ).choose j+(Fintype.card σ).choose (j+1) at hP
      have hD := congrArg (fun z => d*z) hP
      have hS := congrArg (fun z => z*(Fintype.card σ+1).choose (j+1))
        (Nat.sub_add_cancel (show j+1 ≤ d by omega))
      rw [← hcard] at hD hS ⊢
      nlinarith only [he,hw,hD,hS]
    · rw [ite_eq_right hi]
      have hid : d ≤ j+1 := by omega
      rw [twoStep_boundary_above k σ M d n e points hact hp j (by omega) hid,
        twoStep_boundary_above k σ M d n e points hact hp (j+1) (by omega) (by omega)] at he
      have hw := Nat.add_one_mul_choose_eq (Fintype.card σ) (j+1)
      rw [← hcard] at hw
      have hP := Nat.choose_succ_succ (Fintype.card σ) (j+1)
      change (Fintype.card σ+1).choose (j+1+1)=
        (Fintype.card σ).choose (j+1)+(Fintype.card σ).choose (j+1+1) at hP
      have hD := congrArg (fun z => d*z) hP
      have hS := congrArg (fun z => z*(Fintype.card σ+1).choose (j+1+1))
        (Nat.sub_add_cancel (show d ≤ j+1+1 by omega))
      rw [← hcard] at hD hS ⊢
      nlinarith only [he,hw,hD,hS]
end NSP14.Homological
