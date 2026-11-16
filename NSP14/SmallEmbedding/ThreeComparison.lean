module
public import NSP14.SmallEmbedding.LanTuVu
public import NSP14.Ordinary.Closure
public import NSP14.Target.APLowerRows
public import NSP14.Width.FirstResources
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

/-- Actual narrow normalization with a positive internal alphabet; e=3 gives exactly one letter. -/
noncomputable def threeEndpointData (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    NSP14.SmallEmbedding.ThreeData where
  m := S.multiplicity
  d := S.offsetGcd
  u := S.normalizedWidth
  a := S.internalOffsets
  q_one := by rw [S.internalOffsets_card (by omega)];omega
  a_pos := fun _ h => S.internalOffsets_pos h
  a_lt := fun _ h => S.internalOffsets_lt h
  u_lt := by
    have hm := he.trans S.embeddingDimension_le_multiplicity
    have hdiv := Nat.div_le_self S.width S.offsetGcd
    change S.width/S.offsetGcd<S.multiplicity
    omega
  d_pos := S.offsetGcd_pos (by omega)
  offsets_coprime := S.internalOffsets_coprime (by omega)
  coprime := S.offsetGcd_coprime

theorem threeEndpointData_embedding (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    (S.threeEndpointData he hw).q+2=S.embeddingDimension := by
  change S.internalOffsets.card+2=S.embeddingDimension
  rw [S.internalOffsets_card (by omega)]
  omega

theorem threeEndpointData_narrow (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    (S.threeEndpointData he hw).d*(S.threeEndpointData he hw).u+2 ≤ (S.threeEndpointData he hw).m := by
  change S.offsetGcd*S.normalizedWidth+2 ≤ S.multiplicity
  have h := S.width_factor
  have hm := he.trans S.embeddingDimension_le_multiplicity
  have hw' : S.width+2 ≤ S.multiplicity := by omega
  nlinarith only [h,hw']

theorem threeEndpointData_generators (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    (S.threeEndpointData he hw).generators=S.atoms := by
  have hoff : (S.threeEndpointData he hw).offsets=S.normalizedOffsets := S.offsets_reconstruct
  unfold NSP14.SmallEmbedding.ThreeData.generators
  rw [hoff]
  ext n
  constructor
  · intro hn
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
    have hB := S.normalizedOffset_factor hb
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hB
    have hm := S.multiplicity_le (S.atoms_mem ha) ((S.mem_atoms_iff _).mp ha).2.1
    change S.multiplicity+b*S.offsetGcd∈S.atoms
    rw [←heq,Nat.add_sub_of_le hm]
    exact ha
  · intro hn
    have hm := S.multiplicity_le (S.atoms_mem hn) ((S.mem_atoms_iff _).mp hn).2.1
    have hB : n-S.multiplicity∈S.atomOffsets := Finset.mem_image.mpr ⟨n,hn,rfl⟩
    refine Finset.mem_image.mpr ⟨(n-S.multiplicity)/S.offsetGcd,
      Finset.mem_image.mpr ⟨n-S.multiplicity,hB,rfl⟩,?_⟩
    change S.multiplicity+(n-S.multiplicity)/S.offsetGcd*S.offsetGcd=n
    rw [Nat.div_mul_cancel (S.offsetGcd_dvd hB),Nat.add_sub_of_le hm]

theorem threeEndpointData_carrier (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2) :
    (S.threeEndpointData he hw).source.carrier=S.carrier := by
  change AddSubmonoid.closure ((S.threeEndpointData he hw).generators : Set ℕ)=S.carrier
  rw [S.threeEndpointData_generators he hw,S.closure_atoms]

theorem threeEndpointData_completed_totalBetti (he : 3 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2)
    (k : Type) [Field k] (i : ℕ) :
    totalBetti k (S.threeEndpointData he hw).Variables ((S.threeEndpointData he hw).fullG k) i=
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i := by
  rw [(S.threeEndpointData he hw).fullG_totalBetti,
    (S.threeEndpointData he hw).source.carrier_totalBetti S (S.threeEndpointData_carrier he hw) k i,
    S.completed_totalBetti k]
end NSP14.NumericalSemigroup

namespace NSP14.SmallEmbedding
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem three_physical_capacity (he : S.embeddingDimension=3) (hw : S.width ≤ S.multiplicity-2)
    (i : ℕ) (hi : 1 ≤ i) :
    Target.apLowerProfile S.normalizedWidth i ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  have hu : S.normalizedWidth ≤ S.width := Nat.div_le_self _ _
  have ht := S.interval_completed_betti_lower k (by omega) i hi
  rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
  exact (Target.apLowerProfile_monotone i hu).trans ht

theorem three_wide_comparison (he : S.embeddingDimension=3) (hw : S.multiplicity-1 ≤ S.width) :
    let he2 : 2 ≤ S.embeddingDimension := by omega
    ∀ i : ℕ,totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion he2).AtomExponent
        (ModuleCat.of ((S.intervalCompletion he2).FullPolynomialRing k)
          ((S.intervalCompletion he2).FormalTangentAlgebra k)) i := by
  dsimp only
  exact Ordinary.ordinary_actual_completion_betti_le S k (by omega) hw
end NSP14.SmallEmbedding

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- The full-AP half of W_EDGE, on the original completed source and
literal target. The d=1 case uses equality of actual carriers. -/
theorem three_narrow_fullAP_comparison (he : 3 ≤ S.embeddingDimension)
    (hw : S.width ≤ S.multiplicity-2)
    (hu : (S.threeEndpointData (by omega) hw).u=(S.threeEndpointData (by omega) hw).q+1) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  let D := S.threeEndpointData (by omega) hw
  have hDA : D.source.carrier=D.fullAP.source.carrier := D.fullAP_carrier hu
  have hDS : D.source.carrier=S.carrier := S.threeEndpointData_carrier (by omega) hw
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

namespace NSP14.SmallEmbedding
/-- The one-letter resource is paid by the first target row already at u=3. -/
theorem one_first_payment (u : ℕ) (hu : 3 ≤ u) : u+(u-3).choose 2 ≤ u.choose 2 := by
  have h := Width.choose_two_rat u
  have h' := Width.choose_two_rat (u-3)
  have hs : ((u-3:ℕ):ℚ)=(u:ℚ)-3 := by rw [Nat.cast_sub hu];norm_num
  rw [hs] at h'
  have huq : (3:ℚ) ≤ u := by exact_mod_cast hu
  have hp : (u:ℚ)+((u-3).choose 2:ℚ) ≤ (u.choose 2:ℚ) := by nlinarith only [h,h',huq]
  exact_mod_cast hp

theorem one_second_payment (u : ℕ) (hu : 3 ≤ u) : (u-3).choose 2 ≤ u.choose 3 := by
  have hpas := Nat.choose_succ_succ (u-1) 2
  by_cases h : u=3
  · subst u;decide
  have hm := Nat.choose_le_choose 2 (show u-3 ≤ u-1 by omega)
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at hpas
  rw [Nat.sub_add_cancel (show 1 ≤ u by omega)] at hpas
  omega

namespace ThreeData
variable (D : ThreeData) (k : Type) [Field k]
/-- Direct one-internal-variable endpoint comparison. This proves the necessary
LTV comparison, not the paper's three stronger linear numerical estimates. -/
theorem one_actual_profile (hq : D.q=1) (hu : 3 ≤ D.u) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i ≤ Target.apLowerProfile D.u i := by
  obtain ⟨h1,h2,h3⟩ := D.actual_one_rows k hq
  have hP := D.one_coreP_bound k hq
  have hR := D.actualR_one_bound k hq
  by_cases hi1 : i=1
  · subst i
    have h := one_first_payment D.u hu
    exact (show totalBetti k D.Variables (D.fullG k) 1 ≤ D.u.choose 2+1 by omega).trans
      (Target.apLowerProfile_TLOW_one D.u (by omega))
  by_cases hi2 : i=2
  · subst i
    have h := one_second_payment D.u hu
    exact (show totalBetti k D.Variables (D.fullG k) 2 ≤ 2*D.u.choose 3+D.u by omega).trans
      (Target.apLowerProfile_TLOW_two D.u hu)
  by_cases hi3 : i=3
  · subst i
    by_cases hu5 : 5 ≤ D.u
    · have h := Nat.choose_le_choose 2 (Nat.sub_le D.u 3)
      exact (show totalBetti k D.Variables (D.fullG k) 3 ≤ 3*D.u.choose 4+D.u.choose 2 by omega).trans
        (Target.apLowerProfile_TLOW_three D.u hu5)
    · have hz : (D.u-3).choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz] at hR
      have hb : totalBetti k D.Variables (D.fullG k) 3=0 := by omega
      rw [hb];exact Nat.zero_le _
  rw [D.actual_endpoint_above k i (by omega)]
  exact Nat.zero_le _
end ThreeData

variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- All widths, all rows, each actual completed ring in its own minimal variables. -/
theorem three_comparison (he : S.embeddingDimension=3) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  by_cases hw : S.width ≤ S.multiplicity-2
  · let D := S.threeEndpointData (by omega) hw
    have hq : D.q=1 := by
      have h := S.threeEndpointData_embedding (by omega) hw
      change D.q+2=S.embeddingDimension at h
      omega
    have hu : 2 ≤ D.u := by have h := D.q_add_one_le_u;omega
    by_cases hu2 : D.u=2
    · exact S.three_narrow_fullAP_comparison k (by omega) hw (by change D.u=D.q+1;omega) i
    by_cases hi : i=0
    · subst i
      rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
    rw [←S.threeEndpointData_completed_totalBetti (by omega) hw k i]
    exact (D.one_actual_profile k hq (by omega) i (by omega)).trans
      (three_physical_capacity S k he hw i (by omega))
  · exact three_wide_comparison S k he (by omega) i
end NSP14.SmallEmbedding
