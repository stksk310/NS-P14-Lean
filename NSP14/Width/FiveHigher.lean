module
public import NSP14.Width.SparseSecond
public import NSP14.Width.SparseRemainder
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Width
/-- Denominators cleared: C(u,k)/u² increases once u≥k≥2. -/
theorem choose_quadratic_step (u k : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    (u+1)^2*u.choose k ≤ u^2*(u+1).choose k := by
  have hu1 : 1 ≤ u := by omega
  have hc : (u+1)*(u+1-k) ≤ u^2 := by
    calc
      _ ≤ (u+1)*(u-1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ u^2 := by have := Nat.sub_add_cancel hu1; nlinarith only [this]
  have he := Nat.choose_mul_succ_eq u k
  have hm : (u+1-k)*((u+1)^2*u.choose k) ≤ (u+1-k)*(u^2*(u+1).choose k) := by
    calc
      _=((u+1)*(u+1-k))*(u.choose k*(u+1)) := by ring
      _ ≤ u^2*(u.choose k*(u+1)) := Nat.mul_le_mul_right _ hc
      _=_ := by rw [he]; ring
  exact Nat.le_of_mul_le_mul_left hm (by omega)

theorem choose_quadratic_from_eight (u k : ℕ) (hu : 8 ≤ u) (hk : 2 ≤ k) (hk8 : k ≤ 8) :
    u^2*(8:ℕ).choose k ≤ 64*u.choose k := by
  induction u,hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
    have hs := choose_quadratic_step u k hk (by omega)
    have hm1 := Nat.mul_le_mul_left ((u+1)^2) ih
    have hm2 := Nat.mul_le_mul_left 64 hs
    have hm : u^2*((u+1)^2*(8:ℕ).choose k) ≤ u^2*(64*(u+1).choose k) := by
      nlinarith only [hm1,hm2]
    exact Nat.le_of_mul_le_mul_left hm (by positivity)

/-- The first problematic width is checked with the exact old tail,
not the weaker universal quadratic bound. -/
theorem five_wordVolume_eight (D : NSP14.Endpoint.Data) (hq : D.q=3) (hu : D.u=8) :
    D.wordVolume ≤ 14 := by
  have h := D.wordVolume_le_growthVolume
  rw [hq,hu] at h
  norm_num [growthVolume,Finset.sum_range_succ] at h
  exact h
end NSP14.Width
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
/-- All higher rows for five generators, including both cyclic structures.
No antipodal presentation, reflection, or characteristic assumption is used. -/
theorem actual_five_higher (hq : D.q=3) (hu : 8 ≤ D.u) (i : ℕ) (hi : 2 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ i*D.u.choose (i+1) := by
  by_cases hit : 5 < i
  · rw [D.actual_endpoint_above k i (by omega)]
    exact Nat.zero_le _
  have hb := D.actual_positive_rows_add k i (by omega)
  rw [hq] at hb
  have hP := D.coreP_le_wordVolume k
  have hR : D.Rhat+D.u ≤ D.wordVolume := by
    have h := min_le_left (D.wordVolume-D.u) (D.u*(D.coreHeight-2))
    change D.Rhat ≤ _ at h
    have := D.wordVolume_ge_u
    omega
  have hW := D.wordVolume_quadratic_bound
  rw [hq] at hW
  norm_num at hW
  by_cases hi2 : i=2
  · subst i
    norm_num [Nat.choose] at hb
    by_cases hu8 : D.u=8
    · have hw := NSP14.Width.five_wordVolume_eight D hq hu8
      rw [hu8] at *
      norm_num [Nat.choose]
      omega
    · have hu9 : (9:ℚ) ≤ D.u := by exact_mod_cast (show 9 ≤ D.u by omega)
      have hWq : 4*(D.wordVolume:ℚ) ≤ (D.u:ℚ)^2 := by exact_mod_cast hW
      have hPq : (D.coreP k:ℚ) ≤ D.wordVolume := by exact_mod_cast hP
      have hRq : (D.Rhat:ℚ)+D.u ≤ D.wordVolume := by exact_mod_cast hR
      have hbq : (totalBetti k D.Variables (D.fullG k) 2:ℚ)+4 ≤ 6*D.coreP k+4*D.Rhat := by
        exact_mod_cast (show totalBetti k D.Variables (D.fullG k) 2+4≤6*D.coreP k+4*D.Rhat by simpa only [mul_comm] using hb)
      have hp : 0 ≤ 2*((D.u:ℚ)-9)^3+33*((D.u:ℚ)-9)^2+136*((D.u:ℚ)-9)+33 := by positivity
      have hchoose := NSP14.Width.choose_three_rat D.u
      have htarget : (totalBetti k D.Variables (D.fullG k) 2:ℚ) ≤ 2*(D.u.choose 3:ℚ) := by
        nlinarith only [hWq,hPq,hRq,hbq,hp,hchoose]
      exact_mod_cast htarget
  · have hi3 : 3 ≤ i := by omega
    have h4 := NSP14.Width.choose_quadratic_from_eight D.u 4 hu (by decide) (by decide)
    have h5 := NSP14.Width.choose_quadratic_from_eight D.u 5 hu (by decide) (by decide)
    have h6 := NSP14.Width.choose_quadratic_from_eight D.u 6 hu (by decide) (by decide)
    norm_num [Nat.choose] at h4 h5 h6
    interval_cases i <;> norm_num [Nat.choose] at hb ⊢ <;> nlinarith only [hb,hP,hR,hW,h4,h5,h6]
end NSP14.Endpoint.Data
