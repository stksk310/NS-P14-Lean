module
public import NSP14.Width.DenseLexResources
public import NSP14.Width.DensePayment
public import NSP14.Endpoint.FullTransfer
public import NSP14.Endpoint.Normalization
public import NSP14.Target.IntervalAPBetti
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem actual_dense_firstterm (t : ℕ) (hu : D.u=D.q+1+t) (ht2 : 2≤t) (htq : t≤D.q) (hq : 4≤D.q)
    (i : ℕ) (hi : 1 ≤ i) : totalBetti k D.Variables (D.fullG k) i≤ i*D.u.choose (i+1) := by
  by_cases hie : i≤D.q+2
  · obtain ⟨K,hQC,hK2,hK3,hKlarge⟩ := D.dense_core_lex_bound k t hu htq hq
    obtain ⟨_,hP,hR,hR0,_⟩ := D.dense_resources k t hu htq
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
    have hfull := D.actual_core_endpoint_bound k (j+1)
    simp only [coreRemainder,ite_eq_right (by omega : j+1≠0),Nat.add_sub_cancel] at hfull
    have hc := hQC (j+1) (by omega)
    simp only [Nat.add_sub_cancel] at hc
    have hpay := NSP14.Width.dense_payment D.q t (D.coreP k) (D.actualR k) K j hq ht2 htq (by omega)
      hP hR (fun he => ⟨hR0 (by omega),hK2 he⟩) hK3 hKlarge
    have hU : D.u=D.q+t+1 := by omega
    rw [hU]
    simp only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.reduceAdd] at hfull hc hpay ⊢
    nlinarith only [hfull,hc,hpay]
  · rw [D.actual_endpoint_above k i (by omega)]
    exact Nat.zero_le _
end NSP14.Endpoint.Data

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
set_option synthInstance.maxHeartbeats 200000

theorem narrow_dense_firstterm (he : 6≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (t : ℕ) (hu : (S.endpointData (by omega) hw).u=(S.endpointData (by omega) hw).q+1+t)
    (ht2 : 2≤t) (htq : t≤(S.endpointData (by omega) hw).q) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
      i*(S.endpointData (by omega) hw).u.choose (i+1) := by
  let D := S.endpointData (by omega) hw
  have hD : D.q+2=S.embeddingDimension := S.endpointData_embedding (by omega) hw
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
  exact D.actual_dense_firstterm k t hu ht2 htq (by omega) i hi

theorem narrow_dense_comparison (he : 6≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (t : ℕ) (hu : (S.endpointData (by omega) hw).u=(S.endpointData (by omega) hw).q+1+t)
    (ht2 : 2≤t) (htq : t≤(S.endpointData (by omega) hw).q) (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
      totalBetti k (S.intervalCompletion (le_trans (by decide : 2≤6) he)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FullPolynomialRing k)
          ((S.intervalCompletion (le_trans (by decide : 2≤6) he)).FormalTangentAlgebra k)) i := by
  by_cases hi0 : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  have hi : 1 ≤ i := by omega
  have hb := S.narrow_dense_firstterm k he hw t hu ht2 htq i hi
  let D := S.endpointData (by omega) hw
  have hwidth : D.u≤S.width := by
    change S.normalizedWidth≤S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2≤S.embeddingDimension)
    nlinarith only [hf,hd]
  have hm : min S.width (S.multiplicity-1)=S.width := min_eq_left (by omega)
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [hm] at ht
  have hmon := Nat.mul_le_mul_left i (Nat.choose_le_choose (i+1) hwidth)
  have hlead : i*S.width.choose (i+1)≤NSP14.Target.apLowerProfile S.width i := Nat.le_add_right _ _
  exact hb.trans (hmon.trans (hlead.trans ht))

end NSP14.NumericalSemigroup
