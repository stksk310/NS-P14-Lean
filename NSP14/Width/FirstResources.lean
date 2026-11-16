module
public import NSP14.Width.SparseVolume
public import NSP14.Endpoint.CoreWeights
public import NSP14.Endpoint.QuadraticDimension
public import NSP14.Endpoint.PositiveRows
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Width

/-- Exact binomial identity over Q, including u=0. -/
theorem choose_two_rat (u : ℕ) : (u.choose 2 : ℚ)=(u:ℚ)*((u:ℚ)-1)/2 := by
  cases u with
  | zero => norm_num
  | succ n =>
    have hn := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right] at hn
    have h : ((n:ℚ)+1)*n=((n+1).choose 2:ℚ)*2 := by exact_mod_cast hn
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [h]
end NSP14.Width
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- Actual first row, using the same QC and the same original endpoint socle. -/
theorem actual_first_volume_third :
    (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤
      ((D.q:ℚ)+5)*D.wordVolume/3-D.u+((D.q:ℚ)+1)*(D.q+2)/6 := by
  have ht := D.actual_core_endpoint_bound k 1
  simp only [coreRemainder,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self,
    Nat.choose_zero_right,mul_one] at ht
  have htq : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤
      (totalBetti k D.a (D.QCoreModule k) 1:ℚ)+D.coreP k+D.actualR k := by
    exact_mod_cast (show _ from (by simpa only [add_assoc] using ht))
  have hP : (D.coreP k:ℚ)≤D.wordVolume := by exact_mod_cast D.coreP_le_wordVolume k
  have hR : (D.actualR k:ℚ)+D.u≤D.wordVolume := by
    exact_mod_cast (show D.actualR k+D.u≤D.wordVolume by
      have := D.actualR_le_volume k
      have := D.wordVolume_ge_u
      omega)
  have hq : (2:ℚ)≤D.q := by exact_mod_cast D.q_two
  have hb := D.QCore_first_third k
  nlinarith only [htq,hP,hR,hb,hq]

/-- The h2-sensitive first-row bound is also entirely rational, including char 2 and 3. -/
theorem actual_first_volume_fourth :
    (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤
      ((D.q:ℚ)+7)*D.wordVolume/4-D.u+((D.q:ℚ)+1)*(D.q+2)*(D.q+3)/24 := by
  have ht := D.actual_core_endpoint_bound k 1
  simp only [coreRemainder,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self,
    Nat.choose_zero_right,mul_one] at ht
  have htq : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤
      (totalBetti k D.a (D.QCoreModule k) 1:ℚ)+D.coreP k+D.actualR k := by
    exact_mod_cast (show _ from (by simpa only [add_assoc] using ht))
  have hP : (D.coreP k:ℚ)≤D.wordVolume := by exact_mod_cast D.coreP_le_wordVolume k
  have hR : (D.actualR k:ℚ)+D.u≤D.wordVolume := by
    exact_mod_cast (show D.actualR k+D.u≤D.wordVolume by
      have := D.actualR_le_volume k
      have := D.wordVolume_ge_u
      omega)
  have hq : (2:ℚ)≤D.q := by exact_mod_cast D.q_two
  have hh : (D.coreHilbert k 2:ℚ)≤((D.q:ℚ)+1)*D.q/2 := by
    have h := D.coreHilbert_two_bound k
    have h' : (D.coreHilbert k 2:ℚ)≤((D.q+1).choose 2:ℚ) := by exact_mod_cast h
    rw [NSP14.Width.choose_two_rat] at h'
    push_cast at h'
    nlinarith only [h']
  have hb := D.QCore_first_fourth k
  have hweighted := mul_le_mul_of_nonneg_left hh (show 0≤(D.q:ℚ)-1 by linarith)
  have hpweighted := mul_le_mul_of_nonneg_left hP (show 0≤(D.q:ℚ)+3 by positivity)
  nlinarith only [htq,hR,hb,hweighted,hpweighted]

/-- Quadratic resource for the actual first row; a is the real alphabet cardinality. -/
theorem actual_first_quadratic :
    (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤
      ((D.q:ℚ)+5)/3*((D.u:ℚ)^2/(D.q+1))-D.u+
        ((D.q:ℚ)+1)*(D.q+2)/6 := by
  have hquad : ((D.q:ℚ)+1)*D.wordVolume≤(D.u:ℚ)^2 := by
    exact_mod_cast D.wordVolume_quadratic_bound
  have hpos : (0:ℚ)<D.q+1 := by positivity
  have hW : (D.wordVolume:ℚ)≤(D.u:ℚ)^2/(D.q+1) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith only [hquad]
  have hmul := mul_le_mul_of_nonneg_left hW (show 0≤((D.q:ℚ)+5)/3 by positivity)
  have h := D.actual_first_volume_third k
  nlinarith only [h,hmul]
end NSP14.Endpoint.Data
