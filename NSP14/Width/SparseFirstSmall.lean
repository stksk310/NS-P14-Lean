module
public import NSP14.Width.FirstResources
public import NSP14.Width.SparseRemainder
@[expose] public section
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem actual_first_sparse_six (hq : D.q=4) (hu : 10≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have h := D.actual_first_volume_fourth k
  rw [hq] at h
  norm_num at h
  have hw : 6*(D.wordVolume:ℚ)+D.u≤(D.u:ℚ)^2+12 := by
    exact_mod_cast D.wordVolume_q_four hq
  have huQ : (10:ℚ)≤D.u := by exact_mod_cast hu
  have ht : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤(D.u.choose 2:ℚ)+1 := by
    rw [NSP14.Width.choose_two_rat]
    nlinarith only [h,hw,huQ,sq_nonneg ((D.u:ℚ)-10)]
  exact_mod_cast ht

theorem actual_first_sparse_seven (hq : D.q=5) (hu : 12≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have h := D.actual_first_volume_fourth k
  rw [hq] at h
  norm_num at h
  have hw : 6*(D.wordVolume:ℚ)+3*D.u≤(D.u:ℚ)^2+20 := by
    exact_mod_cast D.wordVolume_q_five hq
  have huQ : (12:ℚ)≤D.u := by exact_mod_cast hu
  have ht : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤(D.u.choose 2:ℚ)+1 := by
    rw [NSP14.Width.choose_two_rat]
    nlinarith only [h,hw,huQ]
  exact_mod_cast ht

theorem actual_first_sparse_eight (hq : D.q=6) (hu : 14≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have h := D.actual_first_volume_fourth k
  rw [hq] at h
  norm_num at h
  have hw : 8*(D.wordVolume:ℚ)+2*D.u≤(D.u:ℚ)^2+25 := by
    exact_mod_cast D.wordVolume_q_six hq
  have huQ : (14:ℚ)≤D.u := by exact_mod_cast hu
  have ht : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤(D.u.choose 2:ℚ)+1 := by
    rw [NSP14.Width.choose_two_rat]
    nlinarith only [h,hw,huQ,sq_nonneg ((D.u:ℚ)-14)]
  exact_mod_cast ht

theorem actual_first_sparse_nine (hq : D.q=7) (hu : 16≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have h := D.actual_first_volume_fourth k
  rw [hq] at h
  norm_num at h
  have hw : 8*(D.wordVolume:ℚ)+4*D.u≤(D.u:ℚ)^2+36 := by
    exact_mod_cast D.wordVolume_q_seven hq
  have huQ : (16:ℚ)≤D.u := by exact_mod_cast hu
  have ht : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤(D.u.choose 2:ℚ)+1 := by
    rw [NSP14.Width.choose_two_rat]
    nlinarith only [h,hw,huQ,sq_nonneg ((D.u:ℚ)-16)]
  exact_mod_cast ht

/-- All four small embedding dimensions in the sparse first-row proof. -/
theorem actual_first_sparse_small (he : 6≤D.q+2) (he' : D.q+2≤9)
    (hu : 2*(D.q+2)-2≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have hq : D.q=4 ∨ D.q=5 ∨ D.q=6 ∨ D.q=7 := by omega
  rcases hq with hq|hq|hq|hq
  · exact D.actual_first_sparse_six k hq (by omega)
  · exact D.actual_first_sparse_seven k hq (by omega)
  · exact D.actual_first_sparse_eight k hq (by omega)
  · exact D.actual_first_sparse_nine k hq (by omega)
end NSP14.Endpoint.Data
