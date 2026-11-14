module
public import NSP14.Width.DenseResources
public import NSP14.Width.FirstResources
public import NSP14.Target.IntervalAPBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical BigOperators
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- A nonzero original endpoint socle forces a genuine high-degree QC
basis vector. It therefore takes at least one dimension away from h2. -/
theorem coreHilbert_two_add_five_le_P_of_R_pos (hR : 0<D.actualR k) :
    D.coreHilbert k 2+D.q+2 ≤ D.coreP k := by
  have hH : 3 ≤ D.coreHeight := by
    have h := D.actualR_le_height k
    by_contra hn
    have hz : D.coreHeight-2=0 := by omega
    rw [hz,Nat.mul_zero] at h
    omega
  have hex : ∃ r : Fin D.u, ∃ c : ℕ×ℕ,c∈D.minimalPoints r ∧ 3 ≤ c.1 := by
    by_contra! hn
    have hle : D.coreHeight ≤ 2 := by
      apply Finset.sup_le
      intro r _
      apply Finset.sup_le
      intro c hc
      have := hn r c hc
      omega
    omega
  obtain ⟨r,c,hc,hc3⟩ := hex
  have hm := (D.mem_minimalPoints r c).mp hc
  let p : D.CoreMinimalIndex := ⟨⟨D.decodeCoordinate (r,c),hm.prop⟩,by
    change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
    rw [D.coreCoordinates_decode r c hm.prop]
    exact hm⟩
  let n := D.coreDegree p.val
  have hn3 : 3 ≤ n := by
    change 3 ≤ c.1+c.2+D.epsilon r
    omega
  have hnu : n<D.u := D.coreMinimal_degree_lt p
  have hpos : 1 ≤ D.coreHilbert k n := by
    rw [D.coreHilbert_card]
    let : Nonempty {x : D.CoreMinimalIndex // D.coreDegree x.val=n} := ⟨⟨p,rfl⟩⟩
    exact Nat.card_pos
  have hsub : ({0,1,2,n} : Finset ℕ)⊆Finset.range D.u := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl <;> exact Finset.mem_range.mpr (by omega)
  have hs := Finset.sum_le_sum_of_subset hsub (f:=D.coreHilbert k)
  rw [D.coreHilbert_sum k] at hs
  have hn0 : n≠0 := by omega
  have hn1 : n≠1 := by omega
  have hn2 : n≠2 := by omega
  simp [hn0.symm,hn1.symm,hn2.symm] at hs
  rw [D.coreHilbert_zero k,D.coreHilbert_one k] at hs
  omega

/-- Conditional u=7 improvement is only used when the original R>0. -/
theorem QCore_five_seven_first (hq : D.q=3) (hu : D.u=7) :
    totalBetti k D.a (D.QCoreModule k) 1 ≤ 10 ∧
    (0<D.actualR k → totalBetti k D.a (D.QCoreModule k) 1 ≤ 9) := by
  have hP : D.coreP k ≤ 10 := by
    have h := D.dense_coreP k 3 (by omega) (by omega)
    simpa only [hq] using h
  have hp : (D.coreP k:ℚ) ≤ 10 := by exact_mod_cast hP
  have hb := D.QCore_first_third k
  rw [hq] at hb
  norm_num at hb
  constructor
  · have h : (totalBetti k D.a (D.QCoreModule k) 1:ℚ) ≤ 10 := by linarith
    exact_mod_cast h
  · intro hR
    have hh := D.coreHilbert_two_add_five_le_P_of_R_pos k hR
    rw [hq] at hh
    have hh5 : (D.coreHilbert k 2:ℚ) ≤ 5 := by exact_mod_cast (show D.coreHilbert k 2 ≤ 5 by omega)
    have hb4 := D.QCore_first_fourth k
    rw [hq] at hb4
    norm_num at hb4
    have h : (totalBetti k D.a (D.QCoreModule k) 1:ℚ)<10 := by linarith
    have hn : totalBetti k D.a (D.QCoreModule k) 1<10 := by exact_mod_cast h
    omega

theorem actual_five_small_first (hq : D.q=3) (hu : D.u=6 ∨ D.u=7) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ NSP14.Target.apLowerProfile D.u 1 := by
  have hf := D.actual_core_endpoint_bound k 1
  simp only [coreRemainder,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self,
    Nat.choose_zero_right,mul_one] at hf
  rcases hu with hu|hu
  · obtain ⟨_,hP,_,hR,_⟩ := D.dense_resources k 2 (by omega) (by omega)
    rw [hq] at hP
    have hz := hR (by decide)
    have hp : (D.coreP k:ℚ) ≤ 8 := by exact_mod_cast hP
    have hb := D.QCore_first_third k
    rw [hq] at hb
    norm_num at hb
    have hlt : (totalBetti k D.a (D.QCoreModule k) 1:ℚ)<9 := by linarith
    have hltN : totalBetti k D.a (D.QCoreModule k) 1<9 := by exact_mod_cast hlt
    rw [hu]
    norm_num [NSP14.Target.apLowerProfile,Nat.choose]
    omega
  · have hP := D.dense_coreP k 3 (by omega) (by omega)
    have hR := D.dense_actualR k 3 (by omega) (by omega)
    rw [hq] at hP
    obtain ⟨hb,hbpos⟩ := D.QCore_five_seven_first k hq hu
    rw [hu]
    norm_num [NSP14.Target.apLowerProfile,Nat.choose]
    by_cases hz : D.actualR k=0
    · omega
    · have hb9 := hbpos (by omega)
      omega

/-- The existing actual rank envelope suffices for u=6,7. Its second-row
caps 44 and 68 are weaker than the paper's 40 and 62, but both are paid
by the literal target lower bounds 46 and 77. -/
theorem actual_five_small_positive (hq : D.q=3) (hu : D.u=6 ∨ D.u=7)
    (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ NSP14.Target.apLowerProfile D.u i := by
  by_cases hi1 : i=1
  · subst i
    exact D.actual_five_small_first k hq hu
  by_cases hit : 5 < i
  · rw [D.actual_endpoint_above k i (by omega)]
    exact Nat.zero_le _
  have hb := D.actual_positive_rows_add k i hi
  rw [hq] at hb
  have hW : D.wordVolume ≤ D.u+3 := by
    rcases hu with hu|hu
    · have hw := D.dense_wordVolume 2 (by omega) (by omega)
      omega
    · have hw := D.dense_wordVolume 3 (by omega) (by omega)
      omega
  have hRhat : D.Rhat ≤ 3 := by
    have h := min_le_left (D.wordVolume-D.u) (D.u*(D.coreHeight-2))
    change D.Rhat ≤ _ at h
    omega
  rcases hu with hu|hu
  · obtain ⟨_,hP,_,_,hH⟩ := D.dense_resources k 2 (by omega) (by omega)
    have hz : D.Rhat=0 := by
      unfold Rhat
      have hh : D.coreHeight-2=0 := by omega
      rw [hh,Nat.mul_zero,Nat.min_zero]
    rw [hq] at hP
    rw [hz] at hb
    rw [hu]
    interval_cases i <;> norm_num [NSP14.Target.apLowerProfile,Nat.choose] at hb ⊢ <;> omega
  · have hP := D.dense_coreP k 3 (by omega) (by omega)
    rw [hq] at hP
    rw [hu]
    interval_cases i <;> norm_num [NSP14.Target.apLowerProfile,Nat.choose] at hb ⊢ <;> omega
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem narrow_five_small_comparison (he : S.embeddingDimension=5)
    (hw : S.width ≤ S.multiplicity-2) (hu : S.normalizedWidth=6 ∨ S.normalizedWidth=7)
    (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  by_cases hi0 : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  have hi : 1 ≤ i := by omega
  let D := S.endpointData (by omega) hw
  have hD := S.endpointData_embedding (by omega) hw
  have hq : D.q=3 := by change D.q+2=S.embeddingDimension at hD; omega
  have huD : D.u=6 ∨ D.u=7 := hu
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
        NSP14.Target.apLowerProfile D.u i := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    exact D.actual_five_small_positive k hq huD i hi
  have hwidth : D.u ≤ S.width := by
    change S.normalizedWidth ≤ S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2 ≤ S.embeddingDimension)
    nlinarith only [hf,hd]
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
  exact hb.trans ((NSP14.Target.apLowerProfile_monotone i hwidth).trans ht)
end NSP14.NumericalSemigroup
