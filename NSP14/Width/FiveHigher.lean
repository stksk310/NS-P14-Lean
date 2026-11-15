module
public import NSP14.Width.HigherFromSecond
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
  have hP := D.coreP_le_wordVolume k
  have hR : D.Rhat+D.u ≤ D.wordVolume := by
    have h := min_le_left (D.wordVolume-D.u) (D.u*(D.coreHeight-2))
    change D.Rhat ≤ _ at h
    have := D.wordVolume_ge_u
    omega
  have hie : i ≤ D.q+2 := by omega
  have hue : D.q+2 ≤ D.u := by omega
  by_cases hu8 : D.u=8
  · have hw := NSP14.Width.five_wordVolume_eight D hq hu8
    have hPq : (D.coreP k:ℚ) ≤ 14 := by exact_mod_cast hP.trans hw
    have hRq : (D.Rhat:ℚ)+D.u ≤ 14 := by exact_mod_cast hR.trans hw
    apply D.actual_higher_from_second k 14 hPq hRq hue ?_ i hi hie
    rw [hq,hu8]
    norm_num [Nat.choose]
  · have hu9 : (9:ℚ) ≤ D.u := by exact_mod_cast (show 9 ≤ D.u by omega)
    have hW := D.wordVolume_quadratic_bound
    rw [hq] at hW
    norm_num at hW
    have hWq : 4*(D.wordVolume:ℚ) ≤ (D.u:ℚ)^2 := by exact_mod_cast hW
    have hPq : (D.coreP k:ℚ) ≤ (D.u:ℚ)^2/4 := by
      have hp : (D.coreP k:ℚ) ≤ D.wordVolume := by exact_mod_cast hP
      linarith only [hp,hWq]
    have hRq : (D.Rhat:ℚ)+D.u ≤ (D.u:ℚ)^2/4 := by
      have hr : (D.Rhat:ℚ)+D.u ≤ D.wordVolume := by exact_mod_cast hR
      linarith only [hr,hWq]
    apply D.actual_higher_from_second k ((D.u:ℚ)^2/4) hPq hRq hue ?_ i hi hie
    rw [hq]
    norm_num only [Nat.reduceAdd,Nat.choose, Nat.cast_ofNat]
    rw [NSP14.Width.choose_three_rat]
    have hp : 0 < (2*((D.u:ℚ)-9)^3+33*((D.u:ℚ)-9)^2+
        136*((D.u:ℚ)-9)+33)/6 := by positivity
    have hgap : 2*((D.u:ℚ)*((D.u:ℚ)-1)*((D.u:ℚ)-2)/6)+
        (D.u:ℚ)*4+4-((D.u:ℚ)^2/4)*10 =
        (2*((D.u:ℚ)-9)^3+33*((D.u:ℚ)-9)^2+
          136*((D.u:ℚ)-9)+33)/6 := by ring
    linarith only [hgap,hp]
end NSP14.Endpoint.Data
