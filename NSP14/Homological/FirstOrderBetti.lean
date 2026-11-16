module
public import NSP14.Homological.FirstOrderAction
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
variable (k : Type) [Field k] (r f : ℕ)

theorem firstOrder_totalBetti_zero : totalBetti k (Fin r) (firstOrderModule k r f) 0=1+f := by
  have h := koszul_betti_chain_rank k (Fin r) (firstOrderModule k r f) 0
  have hz := chainBoundaryRank_zero k (coefficientKoszulComplex k (Fin r) (firstOrderModule k r f))
  change koszulBoundaryRank k (Fin r) (firstOrderModule k r f) 0=0 at hz
  rw [Fintype.card_fin,firstOrder_length,firstOrder_boundaryRank k r f 0,hz] at h
  simp only [Nat.zero_add,Nat.choose_zero_right,Nat.choose_one_right,Nat.mul_one,Nat.add_zero] at h
  omega

theorem firstOrder_totalBetti_pos (i : ℕ) (hi : 1 ≤ i) :
    (totalBetti k (Fin r) (firstOrderModule k r f) i : ℤ)=
      (r+f : ℕ)*(r.choose i : ℤ)-(r.choose (i+1) : ℤ) := by
  cases i with
  | zero => omega
  | succ j =>
    have h := koszul_betti_chain_rank k (Fin r) (firstOrderModule k r f) (j+1)
    rw [Fintype.card_fin,firstOrder_length,firstOrder_boundaryRank k r f j,firstOrder_boundaryRank k r f (j+1)] at h
    have hZ : (totalBetti k (Fin r) (firstOrderModule k r f) (j+1) : ℤ)+
        (r.choose (j+1) : ℤ)+(r.choose (j+2) : ℤ)=(1+r+f : ℕ)*(r.choose (j+1) : ℤ) := by exact_mod_cast h
    push_cast at hZ ⊢
    nlinarith

/-- Exact ordinary/square-zero Betti capacity, including r=0 in the
positive rows. This will be applied to the actual Z-action on H0. -/
theorem firstOrder_ordinary_betti (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (Fin r) (firstOrderModule k r 0) i=i*(r+1).choose (i+1) := by
  have hB := firstOrder_totalBetti_pos k r 0 i hi
  simp only [Nat.add_zero] at hB
  have hp := Nat.choose_succ_succ r i
  change (r+1).choose (i+1)=r.choose i+r.choose (i+1) at hp
  have hm := Nat.add_one_mul_choose_eq r i
  have hpZ : ((r+1).choose (i+1) : ℤ)=(r.choose i : ℤ)+(r.choose (i+1) : ℤ) := by exact_mod_cast hp
  have hmZ : (r+1 : ℕ)*(r.choose i : ℤ)=((r+1).choose (i+1) : ℤ)*(i+1 : ℕ) := by exact_mod_cast hm
  have h : (totalBetti k (Fin r) (firstOrderModule k r 0) i : ℤ)=
      (i : ℤ)*((r+1).choose (i+1) : ℤ) := by
    push_cast at hB hmZ
    linarith
  exact_mod_cast h
end NSP14.Homological
