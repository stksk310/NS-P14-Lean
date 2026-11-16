module
public import NSP14.Ordinary.LowRank
@[expose] public section
open scoped BigOperators
namespace NSP14.Ordinary

/-- Zeroth Euler uses the actual generator count; the positive rows use
the harmonic theorem. This keeps the j=1 correction literal. -/
def harmonicWeight (r j t : ℕ) : ℚ :=
  if j=0 then if t=0 then 1 else 0 else ((r-1).choose j : ℚ)*((j:ℚ)/(t+j))

theorem harmonicWeight_zero (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    harmonicWeight r j 0=LowRank.weight r j 0 := by
  have hj0 : j ≠ 0 := by omega
  have hjq : (j:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
  simp only [harmonicWeight,ite_eq_right hj0,Nat.cast_zero,zero_add,div_self hjq,mul_one,LowRank.weight]
  split_ifs with h
  · subst j
    rw [Nat.choose_one_right,Nat.cast_sub hr,Nat.cast_one]
  · rfl

theorem harmonicWeight_step (r j t : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    harmonicWeight r j (t+1)+harmonicWeight r (j-1) t=LowRank.weight r j (t+1) := by
  by_cases hj1 : j=1
  · subst j
    have hrq : ((r-1:ℕ):ℚ)=(r:ℚ)-1 := by rw [Nat.cast_sub hr,Nat.cast_one]
    cases t with
    | zero =>
      norm_num [harmonicWeight,LowRank.weight,Nat.choose_one_right,hrq]
      ring
    | succ t =>
      simp [harmonicWeight,LowRank.weight,Nat.choose_one_right,hrq,Nat.cast_add]
      ring
  · have hj0 : j ≠ 0 := by omega
    have hjm : j-1 ≠ 0 := by omega
    have hjcast : ((j-1:ℕ):ℚ)=(j:ℚ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ j),Nat.cast_one]
    cases t with
    | zero =>
      simp only [harmonicWeight,ite_eq_right hj0,ite_eq_right hjm,Nat.cast_zero,Nat.cast_one,zero_add,
        LowRank.weight,ite_eq_right hj1,hjcast]
      ring
    | succ t =>
      simp only [harmonicWeight,ite_eq_right hj0,ite_eq_right hjm,LowRank.weight,ite_eq_right hj1,Nat.cast_add,Nat.cast_one,hjcast]
      ring

theorem harmonicWeight_sum (r j D : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (H : ℕ → ℚ) (hD : H (D+1)=0) :
    (∑ t ∈ Finset.range (D+1),harmonicWeight r j t*H t)+
      (∑ t ∈ Finset.range (D+1),harmonicWeight r (j-1) t*H (t+1))=
        ∑ t ∈ Finset.range (D+1),LowRank.weight r j t*H t := by
  rw [Finset.sum_range_succ' (fun t => harmonicWeight r j t*H t) D,
    Finset.sum_range_succ (fun t => harmonicWeight r (j-1) t*H (t+1)) D,
    Finset.sum_range_succ' (fun t => LowRank.weight r j t*H t) D,hD,mul_zero,add_zero,
    harmonicWeight_zero r j hr hj]
  have he : (∑ t ∈ Finset.range D,harmonicWeight r j (t+1)*H (t+1))+
      (∑ t ∈ Finset.range D,harmonicWeight r (j-1) t*H (t+1))=
        ∑ t ∈ Finset.range D,LowRank.weight r j (t+1)*H (t+1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← add_mul,harmonicWeight_step r j t hr hj]
  linarith
end NSP14.Ordinary
