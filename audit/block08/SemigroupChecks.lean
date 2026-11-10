module

import NSP14

open NSP14
open scoped BigOperators

namespace NSP14.Block08Audit

-- A conductor is only an existence witness; changing it cannot change multiplicity.
theorem multiplicity_carrier_invariant (S T : NumericalSemigroup)
    (h : S.carrier = T.carrier) : S.multiplicity = T.multiplicity := by
  apply S.multiplicity_eq T.multiplicity_pos
  · change T.multiplicity ∈ S.carrier
    rw [h]
    exact T.multiplicity_mem
  · intro x hx hpos
    apply T.multiplicity_le ?_ hpos
    change x ∈ T.carrier
    rw [← h]
    exact hx

-- Outside the semigroup the total order function has default value zero.
-- Consequently the membership hypothesis on order_eq_zero_iff is substantive.
theorem order_outside (S : NumericalSemigroup) (x : ℕ) (hx : x ∉ S) : S.order x = 0 := by
  classical
  unfold NumericalSemigroup.order
  apply Nat.findGreatest_eq_zero_iff.mpr
  intro n _ _ hlen
  obtain ⟨f, hf, hsum⟩ := hlen
  apply hx
  rw [← hsum]
  exact S.sum_mem Finset.univ f (fun i _ => (hf i).1)

private def exampleS : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b c : ℕ, n = 4 * a + 5 * b + 11 * c}
      zero_mem' := ⟨0, 0, 0, by omega⟩
      add_mem' := by
        rintro x y ⟨a, b, c, hx⟩ ⟨d, e, f, hy⟩
        exact ⟨a + d, b + e, c + f, by omega⟩ }
  conductor := 12
  cofinite n hn := by
    have hm := Nat.mod_lt n (by decide : 0 < 4)
    have he := Nat.mod_add_div n 4
    exact ⟨n / 4 - n % 4, n % 4, 0, by omega⟩

private theorem m_four : exampleS.multiplicity = 4 := by
  apply exampleS.multiplicity_eq (by decide) (show 4 ∈ exampleS from ⟨1, 0, 0, by omega⟩)
  rintro x ⟨a, b, c, hx⟩ hpos
  have hsum : 1 ≤ a + b + c := by omega
  omega

private theorem atom_eleven : exampleS.IsAtom 11 := by
  refine ⟨⟨0, 0, 1, by omega⟩, by decide, ?_⟩
  rintro u ⟨a, b, c, hu⟩ v ⟨d, e, f, hv⟩ heq
  have htotal : 4 * (a + d) + 5 * (b + e) + 11 * (c + f) = 11 := by omega
  by_cases hc : c + f = 0
  · have hB : b + e = 0 ∨ b + e = 1 ∨ b + e = 2 := by omega
    rcases hB with h0 | h1 | h2 <;> omega
  · have hcf : c + f = 1 := by omega
    have hzero : a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 := by omega
    have hsplit : c = 0 ∨ f = 0 := by omega
    rcases hsplit with h0 | h0
    · left; omega
    · right; omega

private theorem order_eleven : exampleS.order 11 = 1 := exampleS.atom_order atom_eleven
private theorem order_four : exampleS.order 4 = 1 := by
  simpa [m_four] using exampleS.order_multiplicity

private theorem length_fifteen : exampleS.HasLength 15 3 := by
  have h5 : 5 ∈ exampleS := ⟨0, 1, 0, by omega⟩
  exact ⟨fun _ => 5, fun _ => ⟨h5, by norm_num⟩, by norm_num⟩

private theorem order_fifteen : exampleS.order 15 = 3 := by
  have hlo := exampleS.length_le_order length_fifteen
  have hhi := exampleS.order_bound (show 15 ∈ exampleS from ⟨0, 3, 0, by omega⟩)
  rw [m_four] at hhi
  omega

private theorem order_nineteen : exampleS.order 19 = 4 := by
  have hl4 := exampleS.length_one (show 4 ∈ exampleS from ⟨1, 0, 0, by omega⟩) (by decide)
  have hlen : exampleS.HasLength 19 4 := by simpa using exampleS.length_add hl4 length_fifteen
  have hlo := exampleS.length_le_order hlen
  have hhi := exampleS.order_bound (show 19 ∈ exampleS from ⟨1, 3, 0, by omega⟩)
  rw [m_four] at hhi
  omega

private theorem terminal_eleven : exampleS.Terminal 11 := by
  refine ⟨atom_eleven.1, ?_⟩
  norm_num [m_four, order_eleven, order_fifteen]

example : exampleS.order 1 = 0 := by
  apply order_outside
  rintro ⟨a, b, c, h⟩
  omega

example : exampleS.NonAperyHead 15 := by
  simpa [m_four] using (exampleS.terminal_iff_head 11).mp terminal_eleven

example : (exampleS.terminalHeadEquiv ⟨11, terminal_eleven⟩).val = 15 := by
  change 11 + exampleS.multiplicity = 15
  rw [m_four]

example : exampleS.jump 0 = 1 ∧ exampleS.jump 11 = 2 ∧ exampleS.jump 15 = 1 := by
  norm_num [NumericalSemigroup.jump, m_four, exampleS.order_zero,
    order_four, order_eleven, order_fifteen, order_nineteen]

-- Without equal jump, neither implication between the numerical live conditions holds.
example : exampleS.order (0 + 11) = exampleS.order 0 + exampleS.order 11 ∧
    ¬ exampleS.order (0 + 11 + exampleS.multiplicity) =
      exampleS.order (0 + exampleS.multiplicity) + exampleS.order 11 := by
  norm_num [m_four, exampleS.order_zero, order_four, order_eleven, order_fifteen]

example : ¬ exampleS.order (11 + 4) = exampleS.order 11 + exampleS.order 4 ∧
    exampleS.order (11 + 4 + exampleS.multiplicity) =
      exampleS.order (11 + exampleS.multiplicity) + exampleS.order 4 := by
  norm_num [m_four, order_four, order_eleven, order_fifteen, order_nineteen]

#print axioms multiplicity_carrier_invariant
#print axioms order_outside

end NSP14.Block08Audit
