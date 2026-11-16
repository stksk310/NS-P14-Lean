module
public import NSP14.Width.FiveHigher
public import NSP14.Width.IntegerPayment
public import NSP14.Additive.CyclicAntipodal
public import NSP14.Target.IntervalAPBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem five_nonAntipodal_volume (hq : D.q=3)
    (ha : ¬NSP14.Additive.CyclicAntipodal D.u D.residueAlphabet) :
    D.wordVolume ≤ NSP14.Width.growthVolume D.u 4 3 := by
  rw [D.wordVolume_tail_shift]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  have hg := NSP14.Additive.fourPoint_growth D.residueAlphabet D.zero_mem_residueAlphabet
    (by rw [D.residueAlphabet_card,hq]) D.residueAlphabet_generates ha (j+1)
  change D.u-(NSP14.Additive.iteratedSum D.residueAlphabet (j+1)).card ≤ D.u-4-3*j
  omega

theorem five_nonAntipodal_volume_remainder (hq : D.q=3) (hu : 8 ≤ D.u)
    (ha : ¬NSP14.Additive.CyclicAntipodal D.u D.residueAlphabet) :
    6*D.wordVolume ≤ D.u^2+D.u+6 := by
  have hvol := D.five_nonAntipodal_volume hq ha
  have he := NSP14.Width.growthVolume_remainder_identity D.u 4 3 (by decide) (by decide) (by omega)
  have hmod := Nat.mod_lt (D.u-4) (by decide : 0<3)
  have hb : ((D.u-4)%3)*(3-(D.u-4)%3) ≤ 2 := by
    interval_cases h : (D.u-4)%3 <;> norm_num
  have hs : D.u-4+4=D.u := by omega
  nlinarith only [he,hvol,hb,hs]

variable (k : Type) [Field k]
theorem actual_five_nonAntipodal_first (hq : D.q=3) (hu : 8 ≤ D.u)
    (ha : ¬NSP14.Additive.CyclicAntipodal D.u D.residueAlphabet) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ D.u.choose 2+1 := by
  have hβ := D.actual_first_volume_fourth k
  rw [hq] at hβ
  norm_num at hβ
  have hW := D.five_nonAntipodal_volume_remainder hq hu ha
  have hWq : 6*(D.wordVolume:ℚ) ≤ (D.u:ℚ)^2+D.u+6 := by exact_mod_cast hW
  apply NSP14.Width.nonAntipodal_integer_payment D.u _ hu
  nlinarith only [hβ,hWq]

end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem narrow_five_nonAntipodal_comparison (he : S.embeddingDimension=5)
    (hw : S.width ≤ S.multiplicity-2) (hu : 8 ≤ S.normalizedWidth)
    (ha : ¬NSP14.Additive.CyclicAntipodal (S.endpointData (by omega) hw).u
      (S.endpointData (by omega) hw).residueAlphabet) (i : ℕ) :
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
  have huD : 8 ≤ D.u := hu
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
        NSP14.Target.apLowerProfile D.u i := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    by_cases hi1 : i=1
    · subst i
      have h := D.actual_five_nonAntipodal_first k hq huD ha
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
end NSP14.NumericalSemigroup
