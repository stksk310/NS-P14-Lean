module
public import NSP14.Endpoint.ArtinWeights
public import NSP14.Endpoint.FirstRow
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreHilbert_tail_sum : D.coreP k=1+∑ n∈Finset.range (D.u-1),D.coreHilbert k (n+1) := by
  have h := D.coreHilbert_sum k
  rw [←Nat.sub_add_cancel (show 1≤D.u from D.u_pos),Finset.sum_range_succ',D.coreHilbert_zero] at h
  omega

theorem coreFirstBound_third : D.coreFirstBound k≤((D.q:ℚ)-1)*D.coreP k/3+
    ((D.q:ℚ)+1)*(D.q+2)/6 :=
  NSP14.Endpoint.weightedFirst_third D.q (D.u-1) (D.coreP k) (D.coreHilbert k) D.q_two
    (by have := D.q_add_one_le_u;have hq : 2≤D.q := D.q_two;omega) (D.coreHilbert_one k) (D.coreHilbert_tail_sum k)

theorem coreFirstBound_fourth : D.coreFirstBound k≤((D.q:ℚ)-1)*D.coreP k/4+
    ((D.q:ℚ)+1)^2/4+((D.q:ℚ)-1)*D.coreHilbert k 2/12 :=
  NSP14.Endpoint.weightedFirst_fourth D.q (D.u-1) (D.coreP k) (D.coreHilbert k) D.q_two
    (by have := D.q_add_one_le_u;have hq : 2≤D.q := D.q_two;omega) (D.coreHilbert_one k) (D.coreHilbert_tail_sum k)

theorem QCore_first_third : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)≤
    ((D.q:ℚ)-1)*D.coreP k/3+((D.q:ℚ)+1)*(D.q+2)/6 :=
  (D.QCore_first_harmonic k).trans (D.coreFirstBound_third k)

theorem QCore_first_fourth : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)≤
    ((D.q:ℚ)-1)*D.coreP k/4+((D.q:ℚ)+1)^2/4+((D.q:ℚ)-1)*D.coreHilbert k 2/12 :=
  (D.QCore_first_harmonic k).trans (D.coreFirstBound_fourth k)

/-- Signed refinement is in Q: the negative high-degree coefficients
are preserved, never replaced by truncated Nat subtraction. -/
theorem QCore_first_signed : (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)-(D.coreP k:ℚ)≤
    (D.q:ℚ)-1+∑ n∈Finset.range (D.u-1),
      ((D.q:ℚ)-(n+1)-2)*(D.coreHilbert k (n+1):ℚ)/(n+2) := by
  have h := sub_le_sub_right (D.QCore_first_harmonic k) (D.coreP k:ℚ)
  change (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)-(D.coreP k:ℚ)≤
    NSP14.Endpoint.weightedFirst D.q (D.u-1) (D.coreHilbert k)-(D.coreP k:ℚ) at h
  rw [NSP14.Endpoint.weightedFirst_signed D.q (D.u-1) (D.coreP k) (D.coreHilbert k)
    (by have hq : 2≤D.q := D.q_two;omega) (D.coreHilbert_tail_sum k)] at h
  exact h
end NSP14.Endpoint.Data
