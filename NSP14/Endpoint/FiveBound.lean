module
public import NSP14.Endpoint.CoreWeights
public import NSP14.Endpoint.QuadraticDimension
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreFirstBound_five (hq : D.q=5) : D.coreFirstBound k-(D.coreP k:ℚ)≤14 := by
  have hh2 := D.coreHilbert_two_bound k
  rw [hq] at hh2
  norm_num at hh2
  have hh1 := D.coreHilbert_one k
  rw [hq] at hh1
  have hN : 2≤D.u-1 := by have := D.q_add_one_le_u;rw [hq] at this;omega
  have hs := NSP14.Endpoint.weightedFirst_five (D.u-1) (D.coreP k) (D.coreHilbert k)
    hN hh1 hh2 (D.coreHilbert_tail_sum k)
  change NSP14.Endpoint.weightedFirst D.q (D.u-1) (D.coreHilbert k)-(D.coreP k:ℚ)≤14
  rw [hq]
  exact hs

theorem QCore_first_five (hq : D.q=5) :
    (totalBetti k D.a (D.QCoreModule k) 1 : ℚ)-(D.coreP k:ℚ)≤14 :=
  (sub_le_sub_right (D.QCore_first_harmonic k) (D.coreP k:ℚ)).trans (D.coreFirstBound_five k hq)
end NSP14.Endpoint.Data
