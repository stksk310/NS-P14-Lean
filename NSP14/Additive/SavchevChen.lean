module
public import NSP14.Additive.ConnectedRepresentatives
public import NSP14.Additive.UnitRepresentatives
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
@[expose] public section
open scoped Pointwise BigOperators Classical
namespace NSP14.Additive

/-- Savchev–Chen for every modulus, proved through the few-subset-sums
connected-sequence argument. The conclusion is a Nat sum for one actual unit. -/
theorem savchevChen {u ℓ : ℕ} (hu : 2 ≤ u) (seq : Fin ℓ → ZMod u)
    (hz : ZeroSumFree seq) (hl : u < 2*ℓ) :
    ∃ c : (ZMod u)ˣ, ∑ i, ((c : ZMod u)*seq i).val < u := by
  let : NeZero u := ⟨by omega⟩
  have hcard : (indexedSubsetSums seq Finset.univ).card ≤ u := by
    have hh := Finset.card_le_univ (indexedSubsetSums seq Finset.univ)
    simpa only [ZMod.card] using hh
  have hsmall : (indexedSubsetSums seq Finset.univ).card < 2*(Finset.univ : Finset (Fin ℓ)).card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using hcard.trans_lt hl
  obtain ⟨a,w,hw,hS,_⟩ := connected_small_representatives hz
    (connected_of_few_subsetSums hz Finset.univ hsmall)
  have hw' (i : Fin ℓ) : 0 < w i ∧ seq i = w i • a := hw i (Finset.mem_univ i)
  have hlength : ℓ ≤ ∑ i, w i := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin ℓ => 1) (g := w) (fun i _ => (hw' i).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hh
  have hdiv : addOrderOf a ∣ u := by
    simpa only [ZMod.card] using (addOrderOf_dvd_card (x := a))
  have horder : addOrderOf a = u := by
    obtain ⟨t,ht⟩ := hdiv
    have ht0 : t ≠ 0 := by intro he; rw [he,mul_zero] at ht; omega
    by_cases ht1 : t = 1
    · simpa [ht1] using ht.symm
    · have ht2 : 2 ≤ t := by omega
      have hh := Nat.mul_le_mul_left (addOrderOf a) ht2
      nlinarith
  have hcop : Nat.Coprime a.val u := by
    have he : addOrderOf a = u / u.gcd a.val := by
      have hh := ZMod.addOrderOf_coe a.val (NeZero.ne u)
      rwa [ZMod.natCast_zmod_val] at hh
    have hg := Nat.div_mul_cancel (Nat.gcd_dvd_left u a.val)
    rw [←he,horder] at hg
    have hu0 : 0 < u := by omega
    have hg1 : u.gcd a.val = 1 := by nlinarith
    rw [Nat.coprime_iff_gcd_eq_one,Nat.gcd_comm]
    exact hg1
  have ha : IsUnit a := by
    rw [←ZMod.natCast_zmod_val a,ZMod.isUnit_iff_coprime]
    exact hcop
  let d := ha.unit
  have hd : (d : ZMod u) = a := ha.unit_spec
  refine ⟨d⁻¹,?_⟩
  have hval (i : Fin ℓ) : ((↑(d⁻¹) : ZMod u)*seq i).val = w i := by
    have hwi : w i < u := by
      have hh := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [horder] at hS
      omega
    have he : (↑(d⁻¹) : ZMod u)*seq i = (w i : ZMod u) := by
      rw [(hw' i).2,nsmul_eq_mul,←hd,mul_left_comm,Units.inv_mul,mul_one]
    rw [he,ZMod.val_natCast_of_lt hwi]
  simp only [hval]
  rwa [horder] at hS

theorem savchevChen_positive {u ℓ : ℕ} (hu : 2 ≤ u) (seq : Fin ℓ → ZMod u)
    (hz : ZeroSumFree seq) (hl : u < 2*ℓ) :
    ∃ c : (ZMod u)ˣ, (∀ i, 0 < ((c : ZMod u)*seq i).val ∧
      ((c : ZMod u)*seq i).val < u) ∧ representativeSum c seq ≤ u-1 := by
  let : NeZero u := ⟨by omega⟩
  obtain ⟨c,hc⟩ := savchevChen hu seq hz hl
  exact ⟨c,hz.positive_representatives c,by unfold representativeSum; omega⟩
end NSP14.Additive
