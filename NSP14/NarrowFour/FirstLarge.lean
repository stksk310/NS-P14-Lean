module
public import NSP14.NarrowFour.FirstCount
public import NSP14.NarrowFour.HigherRows
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.NarrowFour
variable (D : Endpoint.Data) (k : Type) [Field k]

/-- First-row estimate from the same P, sigma, R, and W. -/
theorem actual_first_envelope (hq : D.q=2) :
    (totalBetti k D.Variables (D.fullG k) 1:ℚ) ≤
      ((D.u/2).choose 2:ℚ)+D.u+1+(D.u:ℚ)^2/4 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hC := first_count D k hq a b hab
  have hu : 3 ≤ D.u := by have h := D.q_add_one_le_u;omega
  have hP : (D.coreP k:ℚ)+((D.u/2:ℕ):ℚ)+2 ≤ 2*(D.u:ℚ)+((D.u/2).choose 2:ℚ) := by
    exact_mod_cast (show D.coreP k+D.u/2+2 ≤ 2*D.u+(D.u/2).choose 2 by omega)
  have hσ : (D.internalSigma k hq:ℚ) ≤ ((D.u/2:ℕ):ℚ)+1 := by
    exact_mod_cast (hC.2.2.trans (min_le_left _ _))
  have hR : (D.actualR k:ℚ)+D.u ≤ D.wordVolume := by
    exact_mod_cast (show D.actualR k+D.u ≤ D.wordVolume by
      have := D.actualR_le_volume k
      have := D.wordVolume_ge_u
      omega)
  have hW : 4*(D.wordVolume:ℚ) ≤ (D.u:ℚ)^2+4 := by
    exact_mod_cast distance_volume_four_add D hq
  have hb : (totalBetti k D.Variables (D.fullG k) 1:ℚ) ≤
      (D.coreP k:ℚ)+D.internalSigma k hq+1+D.actualR k := by
    exact_mod_cast D.actual_two_row_one k hq
  linarith only [hP,hσ,hR,hW,hb]

theorem first_large_payment (u : ℕ) (hu : 9 ≤ u) :
    ((u/2).choose 2:ℚ)+(u:ℚ)+1+(u:ℚ)^2/4 ≤ (u.choose 2:ℚ)+1 := by
  have hmod := Nat.mod_add_div u 2
  have hr := Nat.mod_lt u (by omega : 0<2)
  rw [Width.choose_two_rat,Width.choose_two_rat]
  by_cases he : u%2=0
  · have h : (u:ℚ)=2*((u/2:ℕ):ℚ) := by exact_mod_cast (show u=2*(u/2) by omega)
    have h5 : (5:ℚ) ≤ ((u/2:ℕ):ℚ) := by exact_mod_cast (show 5 ≤ u/2 by omega)
    have hp := mul_nonneg (show (0:ℚ) ≤ ((u/2:ℕ):ℚ) by positivity) (show (0:ℚ) ≤ ((u/2:ℕ):ℚ)-5 by linarith)
    rw [h]
    nlinarith only [hp]
  · have h : (u:ℚ)=2*((u/2:ℕ):ℚ)+1 := by exact_mod_cast (show u=2*(u/2)+1 by omega)
    have h4 : (4:ℚ) ≤ ((u/2:ℕ):ℚ) := by exact_mod_cast (show 4 ≤ u/2 by omega)
    have hp := mul_nonneg (show (0:ℚ) ≤ ((u/2:ℕ):ℚ) by positivity) (show (0:ℚ) ≤ ((u/2:ℕ):ℚ)-4 by linarith)
    rw [h]
    nlinarith only [hp,h4]

theorem actual_first_large (hq : D.q=2) (hu : 9 ≤ D.u) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ D.u.choose 2+1 := by
  have hb := (actual_first_envelope D k hq).trans (first_large_payment D.u hu)
  exact_mod_cast hb

theorem actual_first_five (hq : D.q=2) (hu : D.u=5) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ 11 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hP : D.coreP k ≤ 7 := by
    have hp := D.coreP_le_wordVolume k
    have hw := distance_volume_floor D hq
    rw [hu] at hw
    change D.wordVolume ≤ 7 at hw
    omega
  have hσ := sigma_first_bounds D k hq a b hab
  rw [hu] at hσ
  have hr := actualR_zero_small D k hq a b hab (by omega)
  have hb := D.actual_two_row_one k hq
  have hs : D.internalSigma k hq ≤ 3 := hσ.trans (min_le_left _ _)
  omega

theorem narrow_four_first_large (S : NumericalSemigroup) (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) (hu : S.normalizedWidth=5 ∨ 9 ≤ S.normalizedWidth) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 1 ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) 1 := by
  let D := S.endpointData (by omega) hw
  have hq : D.q=2 := by
    have h := S.endpointData_embedding (by omega) hw
    change D.q+2=S.embeddingDimension at h
    omega
  have ht := physical_capacity S k (by omega) hw 1 (by omega)
  change Target.apLowerProfile D.u 1 ≤ _ at ht
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k 1,
    ←D.fullG_totalBetti k]
  change D.u=5 ∨ 9 ≤ D.u at hu
  rcases hu with hu|hu
  · have hb := actual_first_five D k hq hu
    rw [hu] at ht
    exact hb.trans ((show 11 ≤ Target.apLowerProfile 5 1 by decide).trans ht)
  · exact (actual_first_large D k hq hu).trans
      ((Target.apLowerProfile_TLOW_one D.u (by omega)).trans ht)
end NSP14.NarrowFour
