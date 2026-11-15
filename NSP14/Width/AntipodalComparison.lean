module
public import NSP14.Width.AntipodalCore
public import NSP14.Width.FiveNonAntipodal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem positive_residue_mem_iff (b : ℕ) (hb0 : 0<b) (hbu : b<D.u) :
    (b : ZMod D.u)∈D.residueAlphabet ↔ b∈D.a := by
  constructor
  · intro hb
    rcases Finset.mem_insert.mp hb with hb|hb
    · have he := congrArg ZMod.val hb
      rw [ZMod.val_natCast_of_lt hbu,ZMod.val_zero] at he
      omega
    · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hb
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (D.a_lt _ ha),ZMod.val_natCast_of_lt hbu] at hv
      exact hv ▸ ha
  · intro hb
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb)

/-- Recover integer offsets from the same actual cyclic alphabet.
No unit action on the numerical semigroup is used. -/
theorem antipodal_offsets (h t : ℕ) (hu : D.u=2*h) (ht : 0<t) (hth : t<h)
    (hA : D.residueAlphabet={0,(t:ZMod D.u),(h:ZMod D.u),((t+h:ℕ):ZMod D.u)}) :
    D.a={t,h,t+h} := by
  have htu : t<D.u := by omega
  have hhu : h<D.u := by omega
  have hthu : t+h<D.u := by omega
  ext b
  constructor
  · intro hb
    have hm := (D.positive_residue_mem_iff b (D.a_pos _ hb) (D.a_lt _ hb)).mpr hb
    rw [hA] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm ⊢
    rcases hm with he|he|he|he
    · have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (D.a_lt _ hb),ZMod.val_zero] at hv
      have := D.a_pos _ hb
      omega
    · have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (D.a_lt _ hb),ZMod.val_natCast_of_lt htu] at hv
      exact Or.inl hv
    · have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (D.a_lt _ hb),ZMod.val_natCast_of_lt hhu] at hv
      exact Or.inr (Or.inl hv)
    · have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (D.a_lt _ hb),ZMod.val_natCast_of_lt hthu] at hv
      exact Or.inr (Or.inr hv)
  · intro hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with hb|hb|hb
    · rw [hb]
      apply (D.positive_residue_mem_iff t ht htu).mp
      rw [hA]
      simp
    · rw [hb]
      apply (D.positive_residue_mem_iff h (by omega) hhu).mp
      rw [hA]
      simp
    · rw [hb]
      apply (D.positive_residue_mem_iff (t+h) (by omega) hthu).mp
      rw [hA]
      simp

variable (k : Type) [Field k]
/-- First-row payment from the actual normal-form dimension bound.
The exact antipodal generator formula is not assumed. -/
theorem actual_antipodal_first (hq : D.q=3) (hu8 : 8 ≤ D.u)
    (ha : NSP14.Additive.CyclicAntipodal D.u D.residueAlphabet) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ D.u.choose 2+1 := by
  obtain ⟨h,t,hu,ht0,hth,_,hA⟩ := ha
  have hh : 4 ≤ h := by omega
  have hint := D.antipodal_offsets h t hu ht0 hth hA
  have hP := D.antipodal_coreP_bound k h t hu hh ht0 hth hint
  have hPc : (D.coreP k:ℚ) ≤ ((h:ℚ)^2+h+2)/2 := by
    have hc : ((h+1).choose 2:ℚ)=((h:ℚ)+1)*h/2 := by
      rw [NSP14.Width.choose_two_rat]
      push_cast
      ring
    have hp : (D.coreP k:ℚ) ≤ ((h+1).choose 2:ℚ)+1 := by exact_mod_cast hP
    rw [hc] at hp
    linarith
  have hf := D.actual_core_endpoint_bound k 1
  simp only [coreRemainder,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self,
    Nat.choose_zero_right,mul_one] at hf
  have hfq : (totalBetti k D.Variables (D.fullG k) 1:ℚ) ≤
      (totalBetti k D.a (D.QCoreModule k) 1:ℚ)+D.coreP k+D.actualR k := by
    exact_mod_cast (show _ from (by simpa only [add_assoc] using hf))
  have hb := D.QCore_first_third k
  rw [hq] at hb
  norm_num at hb
  have hR : D.actualR k+D.u ≤ D.wordVolume := by
    have := D.actualR_le_volume k
    have := D.wordVolume_ge_u
    omega
  have hW := D.wordVolume_quadratic_bound
  rw [hq,hu] at hW
  have hw : (D.wordVolume:ℚ) ≤ (h:ℚ)^2 := by
    have : D.wordVolume ≤ h^2 := by nlinarith only [hW]
    exact_mod_cast this
  have hr : (D.actualR k:ℚ)+2*h ≤ D.wordVolume := by
    rw [hu] at hR
    exact_mod_cast hR
  rw [hu]
  apply NSP14.Width.antipodal_integer_payment h _ hh
  nlinarith only [hPc,hfq,hb,hw,hr]

end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- All large five-generator widths, combining the actual cyclic structures. -/
theorem narrow_five_large_comparison (he : S.embeddingDimension=5)
    (hw : S.width ≤ S.multiplicity-2) (hu : 8 ≤ S.normalizedWidth) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  by_cases ha : NSP14.Additive.CyclicAntipodal (S.endpointData (by omega) hw).u
      (S.endpointData (by omega) hw).residueAlphabet
  · by_cases hi0 : i=0
    · subst i
      rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
    have hi : 1 ≤ i := by omega
    let D := S.endpointData (by omega) hw
    have hD := S.endpointData_embedding (by omega) hw
    have hq : D.q=3 := by change D.q+2=S.embeddingDimension at hD; omega
    have huD : 8 ≤ D.u := hu
    have hb : totalBetti k S.AtomExponent
        (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
          NSP14.Target.apLowerProfile D.u i := by
      rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
      by_cases hi1 : i=1
      · subst i
        have h := D.actual_antipodal_first k hq huD ha
        have ht : D.u.choose 2+1 ≤ NSP14.Target.apLowerProfile D.u 1 := by
          unfold NSP14.Target.apLowerProfile
          norm_num only [Nat.reduceSub,Nat.reduceAdd,one_mul,Nat.choose_zero_right,Nat.choose_one_right]
          rw [min_eq_left (by omega)]
        exact h.trans ht
      · exact (D.actual_five_higher k hq huD i (by omega)).trans (Nat.le_add_right _ _)
    have hwidth : D.u ≤ S.width := by
      change S.normalizedWidth ≤ S.width
      have hf := S.width_factor
      have hd := S.offsetGcd_pos (by omega : 2 ≤ S.embeddingDimension)
      nlinarith only [hf,hd]
    have ht := S.interval_completed_betti_lower k (by omega) i hi
    rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at ht
    exact hb.trans ((NSP14.Target.apLowerProfile_monotone i hwidth).trans ht)
  · exact S.narrow_five_nonAntipodal_comparison k he hw hu ha i
end NSP14.NumericalSemigroup
