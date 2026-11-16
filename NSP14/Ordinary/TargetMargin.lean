module

public import NSP14.Ordinary.Scalarization

@[expose] public section

namespace NSP14.Ordinary.TargetMargin

open SmallScalar Scalarization

/-!
# The numerical target margin

These are the explicit R_k,L_k of V02 (8.2). The estimate (8.4) follows
by taking first differences in d and using binomial monotonicity.
The actual ordinary target's Betti formula is a separate semantic input.
-/

def target (e d r k : ℕ) : ℚ :=
  ((e : ℚ) - r + k) * (Nat.choose (d + r - 1) k : ℚ) +
    k * (Nat.choose (d + r - 1) (k + 1) : ℚ)

def lower (e r k : ℕ) : ℚ :=
  ((e : ℚ) - 1) * (Nat.choose (r - 1) k : ℚ) - (Nat.choose (r - 1) (k + 1) : ℚ)

theorem choose_succ_cast (n k : ℕ) (hk : 1 ≤ k) :
    (Nat.choose (n + 1) k : ℚ) = (Nat.choose n (k - 1) : ℚ) + Nat.choose n k := by
  have h := Nat.choose_succ_succ' n (k - 1)
  rw [show k - 1 + 1 = k by omega] at h
  exact_mod_cast h

theorem target_zero (e r k : ℕ) (hr : 1 ≤ r) : target e 0 r k = lower e r k := by
  have h := choose_balance (r - 1) (k + 1) (by omega)
  rw [Nat.cast_sub hr] at h
  push_cast at h
  simp only [target, lower, zero_add]
  nlinarith

/-- The exact first difference telescopes the target margin. -/
theorem target_step (e d r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    target e (d + 1) r k - target e d r k =
      ((e : ℚ) + d) * (Nat.choose (d + r - 1) (k - 1) : ℚ) := by
  have hn : d + 1 + r - 1 = (d + r - 1) + 1 := by omega
  have hp := choose_succ_cast (d + r - 1) k hk
  have hq := choose_succ_cast (d + r - 1) (k + 1) (by omega)
  have hb := choose_balance (d + r - 1) k hk
  rw [Nat.cast_sub (show 1 ≤ d + r by omega)] at hb
  push_cast at hb
  unfold target
  rw [hn, hp, hq]
  simp only [Nat.add_sub_cancel]
  nlinarith

theorem capacity_step (e d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * (volume e ((d + 1 : ℕ) : ℚ) + 1) =
      (d : ℚ) * (volume e d + 1) + (e : ℚ) + d := by
  simp only [volume, Nat.cast_add, Nat.cast_one]
  ring

/-- (8.4), proved from the explicit binomial formulas, not assumed as a resource field. -/
theorem target_margin (e d r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (d : ℚ) * (volume e d + 1) * factor r k ≤ target e d r k - lower e r k := by
  induction d with
  | zero => rw [target_zero e r k hr]; simp
  | succ d ih =>
    have hstep := target_step e d r k hr hk
    have hchoose : factor r k ≤ (Nat.choose (d + r - 1) (k - 1) : ℚ) := by
      unfold factor
      exact_mod_cast (Nat.choose_le_choose (k - 1) (show r - 1 ≤ d + r - 1 by omega))
    have hp := mul_le_mul_of_nonneg_left hchoose (by positivity : 0 ≤ (e : ℚ) + d)
    have hcap := capacity_step e d
    have hmul := congrArg (fun q : ℚ => q * factor r k) hcap
    change ((d + 1 : ℕ) : ℚ) * (volume e ((d + 1 : ℕ) : ℚ) + 1) * factor r k ≤ _
    nlinarith

end NSP14.Ordinary.TargetMargin
