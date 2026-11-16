module
public import NSP14.Target.IntervalAPBetti
public import NSP14.Endpoint.Normalization
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
/-- The residue correction is paid by one extra width, including the top row. -/
theorem positiveBettiProfile_upper (A : NSP14.ArithmeticSequence.Data)
    (i : ℕ) (hi : 1 ≤ i) : A.positiveBettiProfile i ≤ i*(A.v+1).choose (i+1) := by
  have hc : (if i ≤ A.residueDefect then (A.residueDefect+1-i)*A.v.choose (i-1)
      else (i-A.residueDefect)*A.v.choose i) ≤ i*A.v.choose i := by
    split_ifs with h
    · have hD := A.residueDefect_le
      have hmul := Nat.mul_le_mul_right (A.v.choose (i-1))
        (show A.residueDefect+1-i ≤ A.v-(i-1) by omega)
      have he := Nat.choose_succ_right_eq A.v (i-1)
      rw [Nat.sub_add_cancel hi] at he
      nlinarith only [hmul,he]
    · exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  unfold positiveBettiProfile
  rw [Nat.choose_succ_succ]
  nlinarith only [hc]
end NSP14.ArithmeticSequence.Data
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem fullAP_offsets (hu : D.u=D.q+1) : D.offsets=Finset.range (D.u+1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    exact Finset.mem_range.mpr (by have := D.offset_le hb; omega)
  · rw [Finset.card_range,D.offsets_card]
    omega

/-- The actual full offset interval is an arithmetic-sequence source,
with the original m and original unrestricted common difference. -/
def fullAP : NSP14.ArithmeticSequence.Data where
  m := D.m
  d := D.d
  v := D.u
  m_two := by have := D.u_pos; have := D.u_lt; omega
  d_pos := D.d_pos
  v_pos := D.u_pos
  v_lt := D.u_lt
  coprime := D.coprime

theorem fullAP_carrier (hu : D.u=D.q+1) : D.source.carrier=D.fullAP.source.carrier := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    intro n hn
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
    exact D.fullAP.generator_mem b (D.offset_le hb)
  · rw [←D.fullAP.source.closure_atoms]
    apply AddSubmonoid.closure_le.mpr
    intro n hn
    obtain ⟨b,hb,rfl⟩ := D.fullAP.atom_eq_generator ((D.fullAP.source.mem_atoms_iff n).mp hn)
    apply D.source_generator
    rw [D.fullAP_offsets hu]
    exact Finset.mem_range.mpr (by change b ≤ D.u at hb; omega)
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- The full-AP half of W_EDGE, on the original completed source and
literal target. The d=1 case uses equality of actual carriers. -/
theorem narrow_fullAP_comparison (he : 5 ≤ S.embeddingDimension)
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
