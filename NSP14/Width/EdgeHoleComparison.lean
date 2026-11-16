module
public import NSP14.Width.EdgeHoleWedgeCount
public import NSP14.Width.EdgeHoleResources
public import NSP14.Target.IntervalAPBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.Endpoint.Data.OneHole
variable {D : NSP14.Endpoint.Data} (H : D.OneHole) (k : Type) [Field k]

/-- The two actual coefficient blocks and the actual unit images are
subtracted from the same chain dimensions before applying full transfer. -/
theorem actual_upper_add (hu : D.u=D.q+2) (delta : ℕ)
    (hP : D.coreP k+delta ≤ D.q+3) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i+delta*(D.q+1).choose i ≤
      i*(D.q+2).choose (i+1)+NSP14.Width.edgeCorrection (H.block false).card (H.block true).card i := by
  have hr0 := H.actual_boundary_rank k (i-1)
  rw [Nat.sub_add_cancel hi] at hr0
  have hr1 := H.actual_boundary_rank k i
  have hc := H.minor_card_pair i hi
  have hchain := koszul_betti_chain_rank k D.a (D.QCoreModule k) i
  rw [(D.QCoreCoefficientEquiv k).finrank_eq,Fintype.card_coe] at hchain
  change _=D.coreP k*D.q.choose i at hchain
  have hf := D.actual_core_endpoint_bound k i
  have hR := (resources (D:=D) k hu).2.1
  simp only [coreRemainder,show i≠0 by omega,ite_false,hR,Nat.zero_mul,add_zero] at hf
  have hpay := NSP14.Width.edge_base_identity D.q i hi
  have hmul := Nat.mul_le_mul_right (D.q.choose i+D.q.choose (i-1)) hP
  have hpas := Nat.choose_succ_left D.q i (by omega)
  nlinarith only [hr0,hr1,hc,hchain,hf,hpay,hmul,hpas]

include H in
theorem actual_positive (hu : D.u=D.q+2) (hq : 3 ≤ D.q) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ NSP14.Target.apLowerProfile D.u i := by
  have hp := H.block_partition
  have hL := H.block_false_card
  have hR := H.block_true_card
  by_cases hedge : H.h=1 ∨ H.h+1=D.u
  · have hP := H.edge_coreP k hu hedge
    have hb := H.actual_upper_add k hu 1 (by omega) i hi
    have hT := NSP14.Width.edgeTopCorrection_le D.q i hq hi
    have hcor : NSP14.Width.edgeCorrection (H.block false).card (H.block true).card i=
        (D.q+1).choose i+NSP14.Width.edgeTopCorrection D.q i := by
      rcases hedge with he|he
      · have hz : (H.block false).card=0 := by omega
        have hn : (H.block true).card=D.q := by omega
        rw [hz,hn,NSP14.Width.edgeCorrection_zero_left]
      · have hz : (H.block true).card=0 := by omega
        have hn : (H.block false).card=D.q := by omega
        rw [hz,hn,NSP14.Width.edgeCorrection_comm,NSP14.Width.edgeCorrection_zero_left]
    rw [hcor] at hb
    unfold NSP14.Target.apLowerProfile
    rw [hu]
    omega
  · have hr : 1 ≤ (H.block false).card := by have := H.pos; omega
    have hs : 1 ≤ (H.block true).card := by have := H.lt; omega
    have hP := (resources (D:=D) k hu).1
    have hb := H.actual_upper_add k hu 0 (by omega) i hi
    have ht0 := NSP14.Width.edgeCorrection_le_choose (H.block false).card (H.block true).card i hr hs hi
    have ht1 := NSP14.Width.edgeCorrection_le_choose_pred (H.block false).card (H.block true).card i hr hs (by omega) hi
    rw [hp] at ht0 ht1
    unfold NSP14.Target.apLowerProfile
    rw [hu]
    omega
end NSP14.Endpoint.Data.OneHole
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem narrow_oneHole_comparison (he : 5 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2)
    (hu : (S.endpointData (by omega) hw).u=(S.endpointData (by omega) hw).q+2) (i : ℕ) :
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
  have hq : 3 ≤ D.q := by change D.q+2=S.embeddingDimension at hD; omega
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
        NSP14.Target.apLowerProfile D.u i := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    exact (D.oneHole hu).actual_positive k hu hq i hi
  have hwidth : D.u ≤ S.width := by
    change S.normalizedWidth ≤ S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2 ≤ S.embeddingDimension)
    nlinarith only [hf,hd]
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
  exact hb.trans ((NSP14.Target.apLowerProfile_monotone i hwidth).trans ht)
end NSP14.NumericalSemigroup
