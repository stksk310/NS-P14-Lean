module
public import NSP14.Width.FiveHoleClassification
public import NSP14.Width.FiveHoleTopRank
public import NSP14.Width.FiveHoleEdge
public import NSP14.Width.FiveSmall
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem QCore_three_euler (hq : D.q=3) :
    totalBetti k D.a (D.QCoreModule k) 2+1=
      totalBetti k D.a (D.QCoreModule k) 1+totalBetti k D.a (D.QCoreModule k) 3 := by
  have h := finite_koszul_bettiEuler_top k D.a (D.QCoreModule k)
    (by rw [Fintype.card_coe]; change 1 ≤ D.q; omega)
  rw [Fintype.card_coe,show D.a.card=3 from hq,bettiEuler_succ,bettiEuler_succ,
    bettiEuler_succ,bettiEuler_zero,D.QCore_betti_zero] at h
  change (totalBetti k D.a (D.QCoreModule k) 3:ℤ)-
    ((totalBetti k D.a (D.QCoreModule k) 2:ℤ)-
      ((totalBetti k D.a (D.QCoreModule k) 1:ℤ)-1))=0 at h
  omega

/-- Both low rows are paid on the original core. The edge omissions use
P ≤ 5, while the two internal omissions use the actual five-generator
kernel and a signed unit minor in the top Koszul differential. -/
theorem fiveHole_low_payments (hq : D.q=3) (hu : D.u=5) :
    totalBetti k D.a (D.QCoreModule k) 1+D.coreP k ≤ 11 ∧
    totalBetti k D.a (D.QCoreModule k) 2+3*D.coreP k ≤ 25 := by
  have hP := D.dense_coreP k 1 (by omega) (by omega)
  rw [hq] at hP
  have he := D.QCore_three_euler k hq
  have hedge (ha : D.a={1,2,3} ∨ D.a={2,3,4}) :
      totalBetti k D.a (D.QCoreModule k) 1+D.coreP k ≤ 11 ∧
      totalBetti k D.a (D.QCoreModule k) 2+3*D.coreP k ≤ 25 := by
    have hp := D.fiveHole_edge_coreP k hq hu ha
    have hpq : (D.coreP k:ℚ) ≤ 5 := by exact_mod_cast hp
    have hb := D.QCore_first_third k
    rw [hq] at hb
    norm_num at hb
    have hlt : (totalBetti k D.a (D.QCoreModule k) 1:ℚ)<7 := by linarith
    have hltN : totalBetti k D.a (D.QCoreModule k) 1<7 := by exact_mod_cast hlt
    have ht := D.QCore_positive_betti_add k 3 (by decide)
    rw [hq] at ht
    norm_num at ht
    omega
  have hinner (flip : Bool) (ha : D.a=if flip then {1,2,4} else {1,3,4}) :
      totalBetti k D.a (D.QCoreModule k) 1+D.coreP k ≤ 11 ∧
      totalBetti k D.a (D.QCoreModule k) 2+3*D.coreP k ≤ 25 := by
    let v := D.fiveHoleVariableEquiv flip ha
    have hv : ∀ i,(v i).val=fiveHoleValues flip i := D.fiveHoleVariableEquiv_val flip ha
    have hb := D.fiveHole_first k hq hu flip v hv
    have ht := D.fiveHole_third_add_three k hq hu flip v hv
    omega
  rcases D.fiveHole_classification hq hu with ha|ha|ha|ha
  · exact hedge (Or.inl ha)
  · exact hinner true ha
  · exact hinner false ha
  · exact hedge (Or.inr ha)

theorem actual_five_hole_positive (hq : D.q=3) (hu : D.u=5)
    (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ NSP14.Target.apLowerProfile D.u i := by
  obtain ⟨_,hP,_,hR,hH⟩ := D.dense_resources k 1 (by omega) (by omega)
  have hz := hR (by decide)
  have hRhat : D.Rhat=0 := by
    unfold Rhat
    rw [show D.coreHeight-2=0 by omega,Nat.mul_zero,Nat.min_zero]
  rw [hq] at hP
  by_cases hi2 : i ≤ 2
  · have hb := D.actual_core_endpoint_bound k i
    obtain ⟨h1,h2⟩ := D.fiveHole_low_payments k hq hu
    simp only [coreRemainder,hq,hz] at hb
    rw [hu]
    interval_cases i <;> norm_num [coreRemainder,NSP14.Target.apLowerProfile,Nat.choose] at hb ⊢ <;> omega
  · by_cases hit : 5 < i
    · rw [D.actual_endpoint_above k i (by omega)]
      exact Nat.zero_le _
    have hb := D.actual_positive_rows_add k i hi
    rw [hq,hRhat] at hb
    rw [hu]
    interval_cases i <;> norm_num [NSP14.Target.apLowerProfile,Nat.choose] at hb ⊢ <;> omega
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem narrow_five_hole_comparison (he : S.embeddingDimension=5)
    (hw : S.width ≤ S.multiplicity-2) (hu : S.normalizedWidth=5) (i : ℕ) :
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
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
        NSP14.Target.apLowerProfile D.u i := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    exact D.actual_five_hole_positive k hq hu i hi
  have hwidth : D.u ≤ S.width := by
    change S.normalizedWidth ≤ S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2 ≤ S.embeddingDimension)
    nlinarith only [hf,hd]
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
  exact hb.trans ((NSP14.Target.apLowerProfile_monotone i hwidth).trans ht)
end NSP14.NumericalSemigroup
