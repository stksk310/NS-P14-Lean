module

public import NSP14.Semigroup.OffsetStabilization
public import NSP14.Semigroup.PolynomialAction

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

theorem leastOffset_zero (r : Fin S.multiplicity) (hr : r.val = 0) : S.leastOffset r = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply S.leastOffset_le r ⟨0, by simpa using S.length_zero⟩
  simpa using hr.symm

theorem leastOffsetLength_zero (r : Fin S.multiplicity) (hr : r.val = 0) :
    S.leastOffsetLength r = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply S.leastOffsetLength_le r
  simpa [S.leastOffset_zero r hr] using S.length_zero

theorem offsetLevel_zero (r : Fin S.multiplicity) (hr : r.val = 0) : S.offsetLevel r = 0 := by
  have := S.offsetLevel_le_length r
  rw [S.leastOffsetLength_zero r hr] at this
  omega

theorem apery_pos_of_residue_ne_zero (r : Fin S.multiplicity) (hr : r.val ≠ 0) :
    0 < S.apery r := by
  have hm := S.apery_mod r
  by_contra hn
  have h0 : S.apery r = 0 := by omega
  simp only [h0, Nat.zero_mod] at hm
  exact hr hm.symm

theorem offset_level_bounds (r : Fin S.multiplicity) (hr : r.val ≠ 0) :
    1 ≤ S.order (S.apery r) ∧ S.order (S.apery r) ≤ S.offsetLevel r ∧
      S.offsetLevel r ≤ S.leastOffsetLength r :=
  ⟨S.order_pos (S.apery_mem r) (S.apery_pos_of_residue_ne_zero r hr),
    S.order_apery_le_offsetLevel r, S.offsetLevel_le_length r⟩

theorem length_remove_multiplicity {b n : ℕ} (f : Fin n → ℕ)
    (hf : ∀ i, f i ∈ S ∧ 0 < f i) (hs : ∑ i, f i = b + n * S.multiplicity)
    (i : Fin n) (hi : f i = S.multiplicity) :
    ∃ k, k < n ∧ S.HasLength (b + k * S.multiplicity) k := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hsum := Fin.sum_univ_succAbove f i
    have hrest : ∑ j : Fin n, f (i.succAbove j) = b + n * S.multiplicity := by
      rw [hi] at hsum
      nlinarith
    exact ⟨n, by omega, ⟨fun j => f (i.succAbove j), fun j => hf _, hrest⟩⟩

/-- Every shortest least-offset representation is an actual longest atomic
factorization, with all multiplicity factors removed. -/
theorem shortest_offset_factors (r : Fin S.multiplicity)
    (f : Fin (S.leastOffsetLength r) → ℕ)
    (hf : ∀ i, f i ∈ S ∧ 0 < f i)
    (hs : ∑ i, f i = S.leastOffset r + S.leastOffsetLength r * S.multiplicity) :
    ∀ i, S.IsAtom (f i) ∧ f i ≠ S.multiplicity := by
  have hm := S.multiplicity_pos
  have hmem := S.sum_mem Finset.univ f (fun i _ => (hf i).1)
  rw [hs] at hmem
  have hupper := S.leastOffset_order_bound hmem r (by
    simpa only [Nat.add_mul_mod_self_right] using (S.leastOffset_spec r).2)
  have hlower := S.length_le_order (S.leastOffsetLength_spec r)
  have he : S.order (S.leastOffset r + S.leastOffsetLength r * S.multiplicity) =
      S.leastOffsetLength r := by nlinarith
  have ha : ∀ i, S.IsAtom (f i) := by
    have hex := S.longest_factors_atoms (x := S.leastOffset r +
      S.leastOffsetLength r * S.multiplicity)
    rw [he] at hex
    exact hex f hf hs
  intro i
  refine ⟨ha i, ?_⟩
  intro hi
  obtain ⟨k, hlt, hk⟩ := S.length_remove_multiplicity f hf hs i hi
  have hmin := S.leastOffsetLength_le r hk
  omega

/-- Telescoping is an equality in naturals; monotonicity supplies every subtraction. -/
theorem jump_excess_sum (r : Fin S.multiplicity) (n : ℕ) :
    (∑ q ∈ Finset.range n, (S.jump (S.apery r + q * S.multiplicity) - 1)) +
      S.order (S.apery r) + n = S.order (S.apery r + n * S.multiplicity) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hle := S.order_add_multiplicity (S.apery_add_multiple r n)
    have hval : S.apery r + (n + 1) * S.multiplicity =
        S.apery r + n * S.multiplicity + S.multiplicity := by ring
    rw [show S.jump (S.apery r + n * S.multiplicity) =
      S.order (S.apery r + n * S.multiplicity + S.multiplicity) -
        S.order (S.apery r + n * S.multiplicity) from rfl]
    rw [hval]
    omega

noncomputable def residueTerminalIndices (r : Fin S.multiplicity) : Finset ℕ :=
  (Finset.range (S.leastOffsetLength r)).filter
    (fun q => S.Terminal (S.apery r + q * S.multiplicity))

theorem jump_eq_one_of_not_terminal {x : ℕ} (hx : x ∈ S) (ht : ¬ S.Terminal x) :
    S.jump x = 1 := by
  have hle := S.order_add_multiplicity hx
  have hn : ¬S.order x + 1 < S.order (x + S.multiplicity) := fun h => ht ⟨hx, h⟩
  unfold jump
  omega

/-- Exact actual residue identity; zero terms are removed only after proving
stabilization and the lower bound on every jump. -/
theorem terminal_residue_sum (r : Fin S.multiplicity) :
    ∑ q ∈ S.residueTerminalIndices r, (S.jump (S.apery r + q * S.multiplicity) - 1) =
      S.offsetLevel r - S.order (S.apery r) := by
  have htel := S.jump_excess_sum r (S.leastOffsetLength r)
  have hstable := S.order_stabilization r (S.leastOffsetLength r) (by omega)
  rw [hstable] at htel
  have hfull : ∑ q ∈ Finset.range (S.leastOffsetLength r),
      (S.jump (S.apery r + q * S.multiplicity) - 1) =
      S.offsetLevel r - S.order (S.apery r) := by omega
  rw [← hfull]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hn
  have ht : ¬ S.Terminal (S.apery r + q * S.multiplicity) := by
    intro ht
    exact hn (Finset.mem_filter.mpr ⟨hq, ht⟩)
  rw [S.jump_eq_one_of_not_terminal (S.apery_add_multiple r q) ht]
  rfl

theorem terminal_index_lt (r : Fin S.multiplicity) (q : ℕ)
    (ht : S.Terminal (S.apery r + q * S.multiplicity)) : q < S.leastOffsetLength r := by
  by_contra hn
  have ho := S.order_stabilization r q (by omega)
  have ho' := S.order_stabilization r (q + 1) (by omega)
  have hval : S.apery r + (q + 1) * S.multiplicity =
      S.apery r + q * S.multiplicity + S.multiplicity := by ring
  rw [hval] at ho'
  have := ht.2
  omega

theorem mem_residueTerminalIndices (r : Fin S.multiplicity) (q : ℕ) :
    q ∈ S.residueTerminalIndices r ↔ S.Terminal (S.apery r + q * S.multiplicity) := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (S.terminal_index_lt r q h), h⟩

end NSP14.NumericalSemigroup
