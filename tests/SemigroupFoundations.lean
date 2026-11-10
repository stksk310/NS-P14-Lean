module

import NSP14

open NSP14
open scoped BigOperators

example (S : NumericalSemigroup) : 0 < S.multiplicity := S.multiplicity_pos
example (S : NumericalSemigroup) : S.aperySet.card = S.multiplicity := S.apery_card

example (S : NumericalSemigroup) : AddSubmonoid.closure (S.atoms : Set ℕ) = S.carrier := S.closure_atoms
example (S : NumericalSemigroup) : S.embeddingDimension ≤ S.multiplicity := S.embeddingDimension_le_multiplicity
example (S : NumericalSemigroup) {x : ℕ} (hx : x ∈ S) :
    ∃ f : Fin (S.order x) → ℕ, (∀ i, S.IsAtom (f i)) ∧ ∑ i, f i = x := S.order_realized_by_atoms hx
example (S : NumericalSemigroup) : (S.highSet).card = S.multiplicity - S.embeddingDimension := S.highSet_card

namespace SemigroupExamples

def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite _ _ := by trivial

theorem naturals_m : naturals.multiplicity = 1 :=
  naturals.multiplicity_eq (by decide) (by trivial) (by intro x _ hx; omega)

theorem naturals_e : naturals.embeddingDimension = 1 := by
  have h := naturals.embeddingDimension_le_multiplicity
  rw [naturals_m] at h
  have := naturals.embeddingDimension_pos
  omega

theorem naturals_order (x : ℕ) : naturals.order x = x := by
  have hlen : naturals.HasLength x x :=
    ⟨fun _ => 1, fun _ => ⟨by trivial, by norm_num⟩, by simp⟩
  have hlo := naturals.length_le_order hlen
  have hhi := naturals.order_bound (show x ∈ naturals from by trivial)
  rw [naturals_m, mul_one] at hhi
  omega

example (x : ℕ) : ¬naturals.Terminal x := by
  intro h
  have ho := h.2
  rw [naturals_order, naturals_order, naturals_m] at ho
  omega

example : naturals.deficit = 0 := by simp [NumericalSemigroup.deficit, naturals_m, naturals_e]

def threeFour : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b : ℕ, n = 3 * a + 4 * b}
      zero_mem' := ⟨0, 0, by omega⟩
      add_mem' := by
        rintro x y ⟨a, b, hx⟩ ⟨c, d, hy⟩
        exact ⟨a + c, b + d, by omega⟩ }
  conductor := 6
  cofinite n hn := by
    have hm := Nat.mod_lt n (by decide : 0 < 3)
    have he := Nat.mod_add_div n 3
    have hc : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hc with h0 | h1 | h2
    · exact ⟨n / 3, 0, by omega⟩
    · exact ⟨n / 3 - 1, 1, by omega⟩
    · exact ⟨n / 3 - 2, 2, by omega⟩

theorem threeFour_m : threeFour.multiplicity = 3 := by
  apply threeFour.multiplicity_eq (by decide) (show 3 ∈ threeFour from ⟨1, 0, by omega⟩)
  rintro x ⟨a, b, hx⟩ hpos
  by_cases ha : a = 0
  · have hb : 1 ≤ b := by omega
    omega
  · have ha1 : 1 ≤ a := by omega
    omega

theorem min_four : IsAperyMin threeFour.carrier 3 4 := by
  refine ⟨⟨0, 1, by omega⟩, ?_⟩
  rintro y ⟨a, b, hy⟩ hmod
  omega

theorem min_eight : IsAperyMin threeFour.carrier 3 8 := by
  refine ⟨⟨0, 2, by omega⟩, ?_⟩
  rintro y ⟨a, b, hy⟩ hmod
  omega

theorem threeFour_apery : threeFour.aperySet = {0, 4, 8} := by
  classical
  have h0 := threeFour.zero_mem_apery
  have h4 : 4 ∈ threeFour.aperySet := (threeFour.mem_aperySet_iff 4).mpr (by simpa [threeFour_m] using min_four)
  have h8 : 8 ∈ threeFour.aperySet := (threeFour.mem_aperySet_iff 8).mpr (by simpa [threeFour_m] using min_eight)
  have hsub : ({0, 4, 8} : Finset ℕ) ⊆ threeFour.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [threeFour.apery_card, threeFour_m]
  norm_num

theorem atom_three : threeFour.IsAtom 3 := by simpa [threeFour_m] using threeFour.multiplicity_atom

theorem atom_four : threeFour.IsAtom 4 := by
  refine ⟨⟨0, 1, by omega⟩, by decide, ?_⟩
  intro u hu v hv hsum
  by_cases h0 : u = 0
  · exact Or.inl h0
  by_cases h1 : v = 0
  · exact Or.inr h1
  have hmu := threeFour.multiplicity_le hu (by omega)
  have hmv := threeFour.multiplicity_le hv (by omega)
  rw [threeFour_m] at hmu hmv
  omega

theorem eight_not_atom : ¬threeFour.IsAtom 8 := by
  intro h
  have hm : 4 ∈ threeFour := ⟨0, 1, by omega⟩
  have he := h.2.2 4 hm 4 hm (by omega)
  omega

theorem threeFour_atoms : threeFour.atoms = {3, 4} := by
  classical
  ext x
  rw [threeFour.mem_atoms_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ha
    by_cases hm : x = 3
    · exact Or.inl hm
    have hap := threeFour.atom_apery ha (by simpa [threeFour_m] using hm)
    rw [threeFour_apery] at hap
    simp only [Finset.mem_insert, Finset.mem_singleton] at hap
    rcases hap with h0 | h4 | h8
    · have := ha.2.1; omega
    · exact Or.inr h4
    · rw [h8] at ha; exact (eight_not_atom ha).elim
  · rintro (rfl | rfl)
    · exact atom_three
    · exact atom_four

theorem threeFour_e : threeFour.embeddingDimension = 2 := by
  unfold NumericalSemigroup.embeddingDimension
  rw [threeFour_atoms]
  norm_num

theorem threeFour_order_eight : threeFour.order 8 = 2 := by
  have hm : 4 ∈ threeFour := ⟨0, 1, by omega⟩
  have hlen : threeFour.HasLength 8 2 := ⟨fun _ => 4, fun _ => ⟨hm, by norm_num⟩, by norm_num⟩
  have hlo := threeFour.length_le_order hlen
  have hhi := threeFour.order_bound (show 8 ∈ threeFour from ⟨0, 2, by omega⟩)
  rw [threeFour_m] at hhi
  omega

example : threeFour.deficit = 1 ∧ (threeFour.degreeSet 1).card = 1 ∧ threeFour.highSet.card = 1 := by
  constructor
  · simp [NumericalSemigroup.deficit, threeFour_m, threeFour_e]
  constructor
  · rw [threeFour.degree_one_card, threeFour_e]
  · rw [threeFour.highSet_card]
    simp [NumericalSemigroup.deficit, threeFour_m, threeFour_e]

-- Block02 now receives a monoid with proved actual multiplicity and embedding dimension.
def threeFour_pairs : AperyPairData threeFour.carrier threeFour.multiplicity threeFour.embeddingDimension := by
  rw [threeFour_m, threeFour_e]
  refine
    { value := fun i : Fin 2 => 4 * i.val
      injective_value := ?_
      value_min := ?_
      pair_min := ?_
      pair_unique := by decide }
  · intro i j h
    change 4 * i.val = 4 * j.val at h
    apply Fin.ext
    omega
  · intro i
    have hi : 4 * i.val = 0 ∨ 4 * i.val = 4 := by omega
    rcases hi with h | h
    · rw [h]; simpa [threeFour_m] using threeFour.zero_min
    · rw [h]; exact min_four
  · intro i j
    have hij : 4 * i.val + 4 * j.val = 0 ∨ 4 * i.val + 4 * j.val = 4 ∨
        4 * i.val + 4 * j.val = 8 := by omega
    rcases hij with h | h | h
    · rw [h]; simpa [threeFour_m] using threeFour.zero_min
    · rw [h]; exact min_four
    · rw [h]; exact min_eight

example : threeFour.embeddingDimension * (threeFour.embeddingDimension - 1) + 1 ≤ threeFour.multiplicity := by
  have : NeZero threeFour.multiplicity := ⟨by have := threeFour.multiplicity_pos; omega⟩
  exact threeFour_pairs.multiplicity_bound

def sixSevenFifteen : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b c : ℕ, n = 6 * a + 7 * b + 15 * c}
      zero_mem' := ⟨0, 0, 0, by omega⟩
      add_mem' := by
        rintro x y ⟨a, b, c, hx⟩ ⟨d, e, f, hy⟩
        exact ⟨a + d, b + e, c + f, by omega⟩ }
  conductor := 30
  cofinite n hn := by
    have hm := Nat.mod_lt n (by decide : 0 < 6)
    have he := Nat.mod_add_div n 6
    exact ⟨n / 6 - n % 6, n % 6, 0, by omega⟩

theorem sixSevenFifteen_m : sixSevenFifteen.multiplicity = 6 := by
  apply sixSevenFifteen.multiplicity_eq (by decide) (show 6 ∈ sixSevenFifteen from ⟨1, 0, 0, by omega⟩)
  rintro x ⟨a, b, c, hx⟩ hpos
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · have hc : 1 ≤ c := by omega
      omega
    · have hb1 : 1 ≤ b := by omega
      omega
  · have ha1 : 1 ≤ a := by omega
    omega

theorem atom_fifteen : sixSevenFifteen.IsAtom 15 := by
  refine ⟨⟨0, 0, 1, by omega⟩, by decide, ?_⟩
  rintro u ⟨a, b, c, hu⟩ v ⟨d, e, f, hv⟩ heq
  have htotal : 6 * (a + d) + 7 * (b + e) + 15 * (c + f) = 15 := by omega
  by_cases hc : c + f = 0
  · have hB : b + e = 0 ∨ b + e = 1 ∨ b + e = 2 := by omega
    rcases hB with h0 | h1 | h2 <;> omega
  · have hcf : c + f = 1 := by omega
    have hzero : a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 := by omega
    have hsplit : c = 0 ∨ f = 0 := by omega
    rcases hsplit with h0 | h0
    · left; omega
    · right; omega

theorem order_twentyone : sixSevenFifteen.order 21 = 3 := by
  have hm : 7 ∈ sixSevenFifteen := ⟨0, 1, 0, by omega⟩
  have hlen : sixSevenFifteen.HasLength 21 3 := ⟨fun _ => 7, fun _ => ⟨hm, by norm_num⟩, by norm_num⟩
  have hlo := sixSevenFifteen.length_le_order hlen
  have hhi := sixSevenFifteen.order_bound (show 21 ∈ sixSevenFifteen from ⟨0, 3, 0, by omega⟩)
  rw [sixSevenFifteen_m] at hhi
  omega

theorem terminal_fifteen : sixSevenFifteen.Terminal 15 := by
  refine ⟨atom_fifteen.1, ?_⟩
  rw [sixSevenFifteen.atom_order atom_fifteen, sixSevenFifteen_m]
  change 2 < sixSevenFifteen.order 21
  rw [order_twentyone]
  decide

example : sixSevenFifteen.NonAperyHead 21 := by
  simpa [sixSevenFifteen_m] using (sixSevenFifteen.terminal_iff_head 15).mp terminal_fifteen
example : sixSevenFifteen.jump 15 = 2 := by
  simp [NumericalSemigroup.jump, sixSevenFifteen_m, sixSevenFifteen.atom_order atom_fifteen, order_twentyone]
example : (sixSevenFifteen.terminalHeadEquiv ⟨15, terminal_fifteen⟩).val = 21 := by
  change 15 + sixSevenFifteen.multiplicity = 21
  rw [sixSevenFifteen_m]

end SemigroupExamples

example (S : NumericalSemigroup) {w : ℕ} (hw : w ∈ S.aperySet) :
    S.order w ≤ S.deficit + 1 := S.apery_order_bound hw

#print axioms NSP14.NumericalSemigroup.zero_mem
#print axioms NSP14.NumericalSemigroup.add_mem
#print axioms NSP14.NumericalSemigroup.multiple_mem
#print axioms NSP14.NumericalSemigroup.positive_exists
#print axioms NSP14.NumericalSemigroup.multiplicity_spec
#print axioms NSP14.NumericalSemigroup.multiplicity_pos
#print axioms NSP14.NumericalSemigroup.multiplicity_mem
#print axioms NSP14.NumericalSemigroup.multiplicity_le
#print axioms NSP14.NumericalSemigroup.multiplicity_eq
#print axioms NSP14.NumericalSemigroup.multiplicity_le_conductor
#print axioms NSP14.NumericalSemigroup.residue_exists
#print axioms NSP14.NumericalSemigroup.apery_spec
#print axioms NSP14.NumericalSemigroup.apery_mem
#print axioms NSP14.NumericalSemigroup.apery_mod
#print axioms NSP14.NumericalSemigroup.apery_min
#print axioms NSP14.NumericalSemigroup.apery_injective
#print axioms NSP14.NumericalSemigroup.apery_card
#print axioms NSP14.NumericalSemigroup.mem_aperySet_iff
#print axioms NSP14.NumericalSemigroup.apery_le
#print axioms NSP14.NumericalSemigroup.decomposition
#print axioms NSP14.NumericalSemigroup.decomposition_unique
#print axioms NSP14.NumericalSemigroup.apery_add_multiple
#print axioms NSP14.NumericalSemigroup.zero_min
#print axioms NSP14.NumericalSemigroup.zero_mem_apery
#print axioms NSP14.NumericalSemigroup.multiplicity_not_apery
#print axioms NSP14.NumericalSemigroup.apery_no_predecessor
#print axioms NSP14.NumericalSemigroup.mem_apery_iff_no_predecessor
#print axioms NSP14.NumericalSemigroup.multiplicity_atom
#print axioms NSP14.NumericalSemigroup.atom_apery
#print axioms NSP14.NumericalSemigroup.mem_atoms_iff
#print axioms NSP14.NumericalSemigroup.multiplicity_mem_atoms
#print axioms NSP14.NumericalSemigroup.atoms_mem
#print axioms NSP14.NumericalSemigroup.mem_closure_atoms
#print axioms NSP14.NumericalSemigroup.closure_atoms
#print axioms NSP14.NumericalSemigroup.atom_mem_of_generates
#print axioms NSP14.NumericalSemigroup.embeddingDimension_pos
#print axioms NSP14.NumericalSemigroup.embeddingDimension_le_multiplicity
#print axioms NSP14.NumericalSemigroup.nonmultiplicity_atoms_card
#print axioms NSP14.NumericalSemigroup.nonmultiplicity_atoms_apery
#print axioms NSP14.NumericalSemigroup.sum_mem
#print axioms NSP14.NumericalSemigroup.length_zero
#print axioms NSP14.NumericalSemigroup.length_one
#print axioms NSP14.NumericalSemigroup.length_le
#print axioms NSP14.NumericalSemigroup.length_multiplicity_bound
#print axioms NSP14.NumericalSemigroup.length_exists
#print axioms NSP14.NumericalSemigroup.order_length
#print axioms NSP14.NumericalSemigroup.length_le_order
#print axioms NSP14.NumericalSemigroup.order_bound
#print axioms NSP14.NumericalSemigroup.order_zero
#print axioms NSP14.NumericalSemigroup.order_pos
#print axioms NSP14.NumericalSemigroup.order_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.length_add
#print axioms NSP14.NumericalSemigroup.order_add
#print axioms NSP14.NumericalSemigroup.order_multiplicity
#print axioms NSP14.NumericalSemigroup.order_add_multiplicity
#print axioms NSP14.NumericalSemigroup.atom_length_bound
#print axioms NSP14.NumericalSemigroup.atom_order
#print axioms NSP14.NumericalSemigroup.order_one_iff_atom
#print axioms NSP14.NumericalSemigroup.order_sum
#print axioms NSP14.NumericalSemigroup.longest_factors_atoms
#print axioms NSP14.NumericalSemigroup.order_realized_by_atoms
#print axioms NSP14.NumericalSemigroup.atomic_length_le
#print axioms NSP14.NumericalSemigroup.degree_zero
#print axioms NSP14.NumericalSemigroup.degree_one
#print axioms NSP14.NumericalSemigroup.degree_zero_card
#print axioms NSP14.NumericalSemigroup.degree_one_card
#print axioms NSP14.NumericalSemigroup.lowSet_subset
#print axioms NSP14.NumericalSemigroup.lowSet_card
#print axioms NSP14.NumericalSemigroup.highSet_eq_sdiff
#print axioms NSP14.NumericalSemigroup.highSet_card
#print axioms NSP14.NumericalSemigroup.degree_two_le_deficit
#print axioms NSP14.NumericalSemigroup.multiplicity_eq_embedding_add_deficit
#print axioms NSP14.NumericalSemigroup.apery_summands
#print axioms NSP14.NumericalSemigroup.apery_predecessor_order
#print axioms NSP14.NumericalSemigroup.degree_exists_le
#print axioms NSP14.NumericalSemigroup.apery_order_bound
#print axioms NSP14.NumericalSemigroup.terminal_iff_head
#print axioms NSP14.NumericalSemigroup.head_predecessor
#print axioms NSP14.NumericalSemigroup.head_sub_terminal
#print axioms NSP14.NumericalSemigroup.terminal_pos
#print axioms NSP14.NumericalSemigroup.terminal_jump
#print axioms NSP14.NumericalSemigroup.terminal_head_degree
#print axioms NSP14.NumericalSemigroup.jump_le_of_live_base
#print axioms NSP14.NumericalSemigroup.jump_le_of_live_head
#print axioms NSP14.NumericalSemigroup.live_iff_of_equal_jump
#print axioms NSP14.NumericalSemigroup.terminalHeadEquiv
