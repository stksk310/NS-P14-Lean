module
public import NSP14.Additive.EndpointVolume
public import Mathlib.Tactic.Ring
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
theorem truncated_step_two (u : ℕ) :
    ∑ j ∈ Finset.range (u+2), (u+2-3-2*j) =
      (u-1)+∑ j ∈ Finset.range u, (u-3-2*j) := by
  rw [show u+2=(u+1)+1 from by omega,Finset.sum_range_succ']
  have he (j : ℕ) : u+2-3-2*(j+1) = u-3-2*j := by omega
  simp only [he,mul_zero,Nat.sub_zero]
  rw [Finset.sum_range_succ]
  have hz : u-3-2*u = 0 := by omega
  rw [hz,add_zero]
  have h0 : u+2-3 = u-1 := by omega
  rw [h0,add_comm]

/-- Closed quadratic bound for the actual three-point growth resource. -/
theorem quadratic_volume_sum (u : ℕ) :
    u+∑ j ∈ Finset.range u, (u-3-2*j) ≤ 1+(u*u)/4 := by
  induction u using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more u ih _ =>
    by_cases hu : u = 0
    · subst u; decide
    have hp : 1 ≤ u := by omega
    rw [truncated_step_two]
    have hs : (u+2)*(u+2) = u*u+4*(u+1) := by ring
    rw [hs]
    have hd : (u*u+4*(u+1))/4 = (u*u)/4+u+1 := by omega
    rw [hd]
    omega
end NSP14.Additive
namespace NSP14.Endpoint.Data
theorem wordVolume_two_bound (D : NSP14.Endpoint.Data) (hq : D.q = 2) :
    D.wordVolume ≤ 1+(D.u*D.u)/4 := by
  have hh := D.wordVolume_growth_bound
  rw [hq] at hh
  norm_num only [Nat.reduceAdd,Nat.reduceDiv] at hh
  exact hh.trans (NSP14.Additive.quadratic_volume_sum D.u)
end NSP14.Endpoint.Data
