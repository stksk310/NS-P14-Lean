module
public import NSP14.Additive.ZeroSumSequence
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
def representativeSum {u ℓ : ℕ} (c : (ZMod u)ˣ) (seq : Fin ℓ → ZMod u) : ℕ :=
  ∑ i, ((c : ZMod u)*seq i).val
def positiveRep {u : ℕ} (a : ZMod u) : ℕ := a.val

theorem zeroSumFree_unit_mul_iff {u ℓ : ℕ} (c : (ZMod u)ˣ) (seq : Fin ℓ → ZMod u) :
    ZeroSumFree (fun i => (c : ZMod u)*seq i) ↔ ZeroSumFree seq := by
  have hm (d : (ZMod u)ˣ) {seq : Fin ℓ → ZMod u} (h : ZeroSumFree seq) :
      ZeroSumFree (fun i => (d : ZMod u)*seq i) := by
    intro I hI he
    apply h I hI
    have he' := congrArg (fun x : ZMod u => (↑(d⁻¹) : ZMod u)*x) he
    simpa only [←Finset.mul_sum, ←mul_assoc, Units.inv_mul, one_mul, mul_zero] using he'
  constructor
  · intro h
    simpa only [←mul_assoc, Units.inv_mul, one_mul] using hm c⁻¹ h
  · exact hm c

theorem ZeroSumFree.positive_representatives {u ℓ : ℕ} [NeZero u]
    {seq : Fin ℓ → ZMod u} (h : ZeroSumFree seq) (c : (ZMod u)ˣ) (i : Fin ℓ) :
    0 < ((c : ZMod u)*seq i).val ∧ ((c : ZMod u)*seq i).val < u := by
  have hn := ((zeroSumFree_unit_mul_iff c seq).mpr h).term_ne_zero i
  exact ⟨ZMod.val_pos.mpr hn, ZMod.val_lt _⟩

theorem no_long_zeroSumFree_mod_one {ℓ : ℕ} (seq : Fin ℓ → ZMod 1)
    (h : ZeroSumFree seq) : ¬1 < 2*ℓ := by
  have hl := h.length_lt_modulus
  omega

theorem zeroSumFree_repeat_unit (u : ℕ) [NeZero u] (a : (ZMod u)ˣ) :
    ZeroSumFree (fun _ : Fin (u-1) => (a : ZMod u)) := by
  have hones : ZeroSumFree (fun _ : Fin (u-1) => (1 : ZMod u)) := by
    intro I hI he
    have hpos : 0 < I.card := hI.card_pos
    have hcard := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hcard
    have hlt : I.card < u := by have hp := NeZero.pos u; omega
    have hd : u ∣ I.card := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using he
    exact Nat.not_dvd_of_pos_of_lt hpos hlt hd
  simpa only [mul_one] using
    (zeroSumFree_unit_mul_iff a (fun _ : Fin (u-1) => (1 : ZMod u))).mpr hones
end NSP14.Additive
