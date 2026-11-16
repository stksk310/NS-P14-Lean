module
public import NSP14.NarrowFour.StandardWords
public import NSP14.NarrowFour.CubicPayment
public import NSP14.Endpoint.TwoRows
public import NSP14.Width.EdgeAP
public import NSP14.Target.APLowerRows
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.NarrowFour
variable (D : Endpoint.Data) (k : Type) [Field k]

/-- All envelopes use the original D, actual QC, and actual endpoint socle. -/
theorem actual_higher_envelopes (hq : D.q=2) :
    (totalBetti k D.Variables (D.fullG k) 2:ℚ) ≤ U2 D.u ∧
    (totalBetti k D.Variables (D.fullG k) 3:ℚ) ≤ U3 D.u ∧
    (totalBetti k D.Variables (D.fullG k) 4:ℚ) ≤ U4 D.u := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hP : (D.coreP k:ℚ) ≤ D.wordVolume := by exact_mod_cast D.coreP_le_wordVolume k
  have hR : (D.actualR k:ℚ)+D.u ≤ D.wordVolume := by
    exact_mod_cast (show D.actualR k+D.u ≤ D.wordVolume by
      have := D.actualR_le_volume k
      have := D.wordVolume_ge_u
      omega)
  have hσ : (D.internalSigma k hq:ℚ)+1 ≤ D.u := by
    exact_mod_cast (show D.internalSigma k hq+1 ≤ D.u by
      have := sigma_le_width D k hq a b hab
      have := D.u_pos
      omega)
  have hW : 4*(D.wordVolume:ℚ) ≤ (D.u:ℚ)^2+4 := by
    exact_mod_cast distance_volume_four_add D hq
  have h2 : (totalBetti k D.Variables (D.fullG k) 2:ℚ) ≤ 
      2*(D.coreP k:ℚ)+D.internalSigma k hq+3*D.actualR k := by
    exact_mod_cast D.actual_two_row_two k hq
  have h3 : (totalBetti k D.Variables (D.fullG k) 3:ℚ) ≤ 
      (D.coreP k:ℚ)+3*D.actualR k := by exact_mod_cast D.actual_two_row_three k hq
  have h4 : (totalBetti k D.Variables (D.fullG k) 4:ℚ) ≤ D.actualR k := by
    exact_mod_cast D.actual_two_row_four k hq
  dsimp [U2,U3,U4]
  exact ⟨by linarith only [h2,hP,hR,hσ,hW],
    by linarith only [h3,hP,hR,hW],by linarith only [h4,hR,hW]⟩

theorem actual_large_higher (hq : D.q=2) (hu : 6 ≤ D.u) (i : ℕ) (hi : 2  ≤  i) :
    totalBetti k D.Variables (D.fullG k) i ≤ i*D.u.choose (i+1) := by
  obtain ⟨h2,h3,h4⟩ := actual_higher_envelopes D k hq
  by_cases h : i=2
  · subst i
    have hp := h2.trans (second_payment D.u hu).le
    dsimp [T] at hp
    exact_mod_cast hp
  by_cases h' : i=3
  · subst i
    have hp := h3.trans (third_payment D.u hu)
    dsimp [T] at hp
    exact_mod_cast hp
  by_cases h'' : i=4
  · subst i
    have hp := h4.trans (fourth_payment D.u hu)
    dsimp [T] at hp
    exact_mod_cast hp
  rw [D.actual_endpoint_above k i (by omega)]
  exact Nat.zero_le _

/-- Small high rows before the physical interval target is selected. -/
theorem actual_small_higher (hq : D.q=2) (hu : D.u ≤ 5) :
    totalBetti k D.Variables (D.fullG k) 2 ≤ 18 ∧
    totalBetti k D.Variables (D.fullG k) 3 ≤ 7 ∧
    totalBetti k D.Variables (D.fullG k) 4=0 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hr := actualR_zero_small D k hq a b hab hu
  have hP : D.coreP k ≤ 7 := by
    have hp := D.coreP_le_wordVolume k
    have hw := distance_volume_floor D hq
    have hsq : D.u*D.u ≤ 25 := Nat.mul_self_le_mul_self hu
    have hd := Nat.div_le_div_right (c:=4) hsq
    omega
  have hσ : D.internalSigma k hq ≤ 4 := by
    have := sigma_le_width D k hq a b hab
    omega
  have h2 := D.actual_two_row_two k hq
  have h3 := D.actual_two_row_three k hq
  have h4 := D.actual_two_row_four k hq
  exact ⟨by omega,by omega,by omega⟩

theorem actual_width_four_higher (hq : D.q=2) (hu : D.u=4) :
    totalBetti k D.Variables (D.fullG k) 2 ≤ 12 ∧
    totalBetti k D.Variables (D.fullG k) 3 ≤ 5 ∧
    totalBetti k D.Variables (D.fullG k) 4=0 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hr := actualR_zero_small D k hq a b hab (by omega)
  have hP : D.coreP k ≤ 5 := by
    have hp := D.coreP_le_wordVolume k
    have hw := distance_volume_floor D hq
    rw [hu] at hw
    norm_num at hw
    omega
  have hσ : D.internalSigma k hq ≤ 2 := by
    have ht := socle_triangle_card D k hq a b hab
    by_contra hn
    have hl := Nat.choose_le_choose 2 (show 4 ≤ D.internalSigma k hq+1 by omega)
    change 6 ≤ (D.internalSigma k hq+1).choose 2 at hl
    omega
  have h2 := D.actual_two_row_two k hq
  have h3 := D.actual_two_row_three k hq
  have h4 := D.actual_two_row_four k hq
  exact ⟨by omega,by omega,by omega⟩

end NSP14.NarrowFour

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- The full-AP half of W_EDGE, on the original completed source and
literal target. The d=1 case uses equality of actual carriers. -/
theorem narrow_four_fullAP_comparison (he : 4 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2)
    (hu : (S.endpointData (by omega) hw).u=(S.endpointData (by omega) hw).q+1) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  let D := S.endpointData (by omega) hw
  have hDA : D.source.carrier=D.fullAP.source.carrier := D.fullAP_carrier hu
  have hDS : D.source.carrier=S.carrier := S.endpointData_carrier (by omega) hw
  have hSA : S.carrier=D.fullAP.source.carrier := hDS.symm.trans hDA
  have hSm : S.multiplicity=D.m := rfl
  have hSw : S.width=D.d*D.u := by
    change S.width=S.offsetGcd*S.normalizedWidth
    rw [Nat.mul_comm,S.width_factor]
  by_cases hd : D.d=1
  · have hV : min S.width (S.multiplicity-1)=D.u := by
      rw [hSw,hd,one_mul,hSm]
      exact min_eq_left (by have := D.u_lt; omega)
    have hST : S.carrier=(S.intervalCompletion (by omega)).carrier := by
      rw [hSA]
      ext n
      change (∃ l j : ℕ,j ≤ D.u*l ∧ n=l*D.m+j*D.d) ↔
        (∃ l j : ℕ,j ≤ min S.width (S.multiplicity-1)*l ∧ n=l*S.multiplicity+j*1)
      rw [hV,hSm,hd]
    rw [←S.completed_totalBetti k,←(S.intervalCompletion (by omega)).completed_totalBetti k,
      S.carrier_totalBetti _ hST k i]
  by_cases hi : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  have hip : 1 ≤ i := by omega
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
        i*(D.u+1).choose (i+1) := by
    rw [←S.completed_totalBetti k,S.carrier_totalBetti D.fullAP.source hSA k i,
      D.fullAP.cone_totalBetti_pos k i hip]
    exact D.fullAP.positiveBettiProfile_upper i hip
  have hd2 : 2 ≤ D.d := by have := D.d_pos; omega
  have hV : D.u+1 ≤ S.width := by
    have hp := D.u_pos
    nlinarith only [hSw,hd2,hp]
  have hmin : min S.width (S.multiplicity-1)=S.width := min_eq_left (by omega)
  have ht := S.interval_completed_betti_lower k (by omega) i hip
  rw [hmin] at ht
  exact hb.trans ((Nat.mul_le_mul_left i (Nat.choose_le_choose (i+1) hV)).trans
    ((Nat.le_add_right _ _).trans ht))
end NSP14.NumericalSemigroup

namespace NSP14.NarrowFour
variable (S : NumericalSemigroup) (k : Type) [Field k]

/-- The same source's full physical interval has enough capacity for every base row. -/
theorem physical_capacity (he : 4 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2) (i : ℕ) (hi : 1 ≤ i) :
    Target.apLowerProfile (S.endpointData he hw).u i ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  have hu : (S.endpointData he hw).u ≤ S.width := by
    have hd := (S.endpointData he hw).d_pos
    have hmul := Nat.mul_le_mul_right (S.endpointData he hw).u hd
    have hf : (S.endpointData he hw).d*(S.endpointData he hw).u=S.width := by
      change S.offsetGcd*S.normalizedWidth=S.width
      rw [Nat.mul_comm,S.width_factor]
    simpa only [one_mul,hf] using hmul
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
  exact (Target.apLowerProfile_monotone i hu).trans ht

/-- N4 higher rows on the original completed source and literal completed target. -/
theorem narrow_four_higher (he : S.embeddingDimension=4)
    (hw : S.width ≤ S.multiplicity-2) (i : ℕ) (hi : 2 ≤ i) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  let D := S.endpointData (by omega) hw
  have hq : D.q=2 := by
    have h := S.endpointData_embedding (by omega) hw
    change D.q+2=S.embeddingDimension at h
    omega
  have hu : 3 ≤ D.u := by have h := D.q_add_one_le_u;omega
  by_cases h3 : D.u=3
  · exact S.narrow_four_fullAP_comparison k (by omega) hw (by change D.u=D.q+1;omega) i
  have hsource : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i =
      totalBetti k D.Variables (D.fullG k) i := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k i,
      ←D.fullG_totalBetti k]
  rw [hsource]
  have htarget := physical_capacity S k (by omega) hw i (by omega)
  change Target.apLowerProfile D.u i ≤ _ at htarget
  by_cases hlarge : 6 ≤ D.u
  · exact (actual_large_higher D k hq hlarge i hi).trans
      ((Nat.le_add_right _ _).trans htarget)
  by_cases h4 : D.u=4
  · obtain ⟨h2,hthree,hfour⟩ := actual_width_four_higher D k hq h4
    rw [h4] at htarget
    by_cases hi2 : i=2
    · subst i;exact h2.trans ((show 12 ≤ Target.apLowerProfile 4 2 by decide).trans htarget)
    by_cases hi3 : i=3
    · subst i;exact hthree.trans ((show 5 ≤ Target.apLowerProfile 4 3 by decide).trans htarget)
    by_cases hi4 : i=4
    · subst i;rw [hfour];exact Nat.zero_le _
    rw [D.actual_endpoint_above k i (by omega)]
    exact Nat.zero_le _
  · have h5 : D.u=5 := by omega
    obtain ⟨h2,hthree,hfour⟩ := actual_small_higher D k hq (by omega)
    rw [h5] at htarget
    by_cases hi2 : i=2
    · subst i;exact h2.trans ((show 18 ≤ Target.apLowerProfile 5 2 by decide).trans htarget)
    by_cases hi3 : i=3
    · subst i;exact hthree.trans ((show 7 ≤ Target.apLowerProfile 5 3 by decide).trans htarget)
    by_cases hi4 : i=4
    · subst i;rw [hfour];exact Nat.zero_le _
    rw [D.actual_endpoint_above k i (by omega)]
    exact Nat.zero_le _
end NSP14.NarrowFour
