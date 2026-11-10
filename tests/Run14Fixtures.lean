module

public import NSP14
public import tests.Run12Fixtures

@[expose] public section

open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary
open scoped Classical BigOperators

namespace Run14Fixtures
namespace rankTwo

def allowed : Finset ℕ := {0,6,7,11,12,13,14}

def source : NumericalSemigroup where
  carrier :=
    { carrier := {n | n ∈ allowed ∨ 17 ≤ n}
      zero_mem' := Or.inl (by decide)
      add_mem' := by
        intro x y hx hy
        change x+y ∈ allowed ∨ 17 ≤ x+y
        change x ∈ allowed ∨ 17 ≤ x at hx
        change y ∈ allowed ∨ 17 ≤ y at hy
        simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
        omega }
  conductor := 17
  cofinite _ h := Or.inr h

theorem multiplicity : source.multiplicity = 6 := by
  apply source.multiplicity_eq (by decide) (Or.inl (by decide))
  intro n hn hp
  change n ∈ allowed ∨ 17 ≤ n at hn
  simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

def weight (n : ℕ) : ℕ := [0,0,0,0,0,0,1,1,0,0,0,1,2,2,2,0,0,2,3,3,3,3,2][n]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem weight_step : ∀ x ∈ Finset.range 23, ∀ y ∈ Finset.range 23,
    (x ∈ allowed ∨ 17 ≤ x) → 0 < x → (y ∈ allowed ∨ 17 ≤ y) → x+y ≤ 22 →
      weight y+1 ≤ weight (x+y) := by decide

theorem order_le (n : ℕ) (hn : n ∈ source) (hb : n ≤ 22) : source.order n ≤ weight n := by
  apply Run12Fixtures.length_weight_bound source 22 weight ?_ (source.order_length hn) hb
  intro a ha hp b hB hab
  exact weight_step a (Finset.mem_range.mpr (by omega)) b (Finset.mem_range.mpr (by omega)) ha hp hB hab

theorem order_7 : source.order 7 = 1 := by
  have hu := order_le 7 (by change 7 ∈ allowed ∨ 17 ≤ 7; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 7 1 from
    ⟨![7], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 17 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_11 : source.order 11 = 1 := by
  have hu := order_le 11 (by change 11 ∈ allowed ∨ 17 ≤ 11; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 11 1 from
    ⟨![11], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 17 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_14 : source.order 14 = 2 := by
  have hu := order_le 14 (by change 14 ∈ allowed ∨ 17 ≤ 14; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 14 2 from
    ⟨![7,7], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 17 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_21 : source.order 21 = 3 := by
  have hu := order_le 21 (by change 21 ∈ allowed ∨ 17 ≤ 21; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 21 3 from
    ⟨![7,7,7], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 17 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_22 : source.order 22 = 2 := by
  have hu := order_le 22 (by change 22 ∈ allowed ∨ 17 ≤ 22; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 22 2 from
    ⟨![11,11], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 17 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem apery : source.aperySet = {0,7,11,14,21,22} := by
  have hs : ({0,7,11,14,21,22} : Finset ℕ) ⊆ source.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact source.zero_mem_apery
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 7 ∈ allowed ∨ 17 ≤ 7; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 17 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 11 ∈ allowed ∨ 17 ≤ 11; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 17 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 14 ∈ allowed ∨ 17 ≤ 14; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 17 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 21 ∈ allowed ∨ 17 ≤ 21; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 17 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 22 ∈ allowed ∨ 17 ≤ 22; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 17 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
  symm
  apply Finset.eq_of_subset_of_card_le hs
  rw [source.apery_card, multiplicity]
  decide

theorem degree_1 : source.degreeSet 1 = {7,11} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_7, order_11, order_14, order_21, order_22]
  decide

theorem degree_2 : source.degreeSet 2 = {14,22} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_7, order_11, order_14, order_21, order_22]
  decide

theorem embedding : source.embeddingDimension = 3 := by
  have hc := source.degree_one_card
  rw [degree_1] at hc
  norm_num at hc
  have := source.embeddingDimension_pos
  omega

theorem quadratic_dimension (k : Type*) [Field k] :
    Module.finrank k (source.qDegree k 2) = 2 := by
  rw [source.qDegree_finrank, degree_2]
  decide

theorem cut_rank : source.actualCutRank = 2 := by
  unfold actualCutRank
  rw [degree_2]
  decide

theorem atoms : source.atoms = {6,7,11} := by
  have he := Finset.insert_erase source.multiplicity_mem_atoms
  rw [← source.degree_one, degree_1, multiplicity] at he
  exact he.symm

theorem closure_generators : AddSubmonoid.closure ({6,7,11} : Set ℕ) = source.carrier := by
  rw [← source.closure_atoms, atoms]
  simp only [Finset.coe_insert, Finset.coe_singleton]

end rankTwo
namespace evenMaximal

def allowed : Finset ℕ := {0,8,9,11,16,17,18,19,20,22}

def source : NumericalSemigroup where
  carrier :=
    { carrier := {n | n ∈ allowed ∨ 24 ≤ n}
      zero_mem' := Or.inl (by decide)
      add_mem' := by
        intro x y hx hy
        change x+y ∈ allowed ∨ 24 ≤ x+y
        change x ∈ allowed ∨ 24 ≤ x at hx
        change y ∈ allowed ∨ 24 ≤ y at hy
        simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
        omega }
  conductor := 24
  cofinite _ h := Or.inr h

theorem multiplicity : source.multiplicity = 8 := by
  apply source.multiplicity_eq (by decide) (Or.inl (by decide))
  intro n hn hp
  change n ∈ allowed ∨ 24 ≤ n at hn
  simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

def weight (n : ℕ) : ℕ := [0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,2,2,2,2,2,0,2,0,3,3,3,3,3,3,3,3][n]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem weight_step : ∀ x ∈ Finset.range 32, ∀ y ∈ Finset.range 32,
    (x ∈ allowed ∨ 24 ≤ x) → 0 < x → (y ∈ allowed ∨ 24 ≤ y) → x+y ≤ 31 →
      weight y+1 ≤ weight (x+y) := by decide

theorem order_le (n : ℕ) (hn : n ∈ source) (hb : n ≤ 31) : source.order n ≤ weight n := by
  apply Run12Fixtures.length_weight_bound source 31 weight ?_ (source.order_length hn) hb
  intro a ha hp b hB hab
  exact weight_step a (Finset.mem_range.mpr (by omega)) b (Finset.mem_range.mpr (by omega)) ha hp hB hab

theorem order_9 : source.order 9 = 1 := by
  have hu := order_le 9 (by change 9 ∈ allowed ∨ 24 ≤ 9; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 9 1 from
    ⟨![9], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_11 : source.order 11 = 1 := by
  have hu := order_le 11 (by change 11 ∈ allowed ∨ 24 ≤ 11; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 11 1 from
    ⟨![11], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_18 : source.order 18 = 2 := by
  have hu := order_le 18 (by change 18 ∈ allowed ∨ 24 ≤ 18; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 18 2 from
    ⟨![9,9], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_20 : source.order 20 = 2 := by
  have hu := order_le 20 (by change 20 ∈ allowed ∨ 24 ≤ 20; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 20 2 from
    ⟨![11,9], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_22 : source.order 22 = 2 := by
  have hu := order_le 22 (by change 22 ∈ allowed ∨ 24 ≤ 22; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 22 2 from
    ⟨![11,11], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_29 : source.order 29 = 3 := by
  have hu := order_le 29 (by change 29 ∈ allowed ∨ 24 ≤ 29; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 29 3 from
    ⟨![11,9,9], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_31 : source.order 31 = 3 := by
  have hu := order_le 31 (by change 31 ∈ allowed ∨ 24 ≤ 31; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 31 3 from
    ⟨![11,11,9], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 24 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem apery : source.aperySet = {0,9,11,18,20,22,29,31} := by
  have hs : ({0,9,11,18,20,22,29,31} : Finset ℕ) ⊆ source.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact source.zero_mem_apery
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 9 ∈ allowed ∨ 24 ≤ 9; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 11 ∈ allowed ∨ 24 ≤ 11; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 18 ∈ allowed ∨ 24 ≤ 18; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 20 ∈ allowed ∨ 24 ≤ 20; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 22 ∈ allowed ∨ 24 ≤ 22; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 29 ∈ allowed ∨ 24 ≤ 29; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 31 ∈ allowed ∨ 24 ≤ 31; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 24 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
  symm
  apply Finset.eq_of_subset_of_card_le hs
  rw [source.apery_card, multiplicity]
  decide

theorem degree_1 : source.degreeSet 1 = {9,11} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_9, order_11, order_18, order_20, order_22, order_29, order_31]
  decide

theorem degree_2 : source.degreeSet 2 = {18,20,22} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_9, order_11, order_18, order_20, order_22, order_29, order_31]
  decide

theorem embedding : source.embeddingDimension = 3 := by
  have hc := source.degree_one_card
  rw [degree_1] at hc
  norm_num at hc
  have := source.embeddingDimension_pos
  omega

theorem quadratic_dimension (k : Type*) [Field k] :
    Module.finrank k (source.qDegree k 2) = 3 := by
  rw [source.qDegree_finrank, degree_2]
  decide

theorem cut_rank : source.actualCutRank = 2 := by
  unfold actualCutRank
  rw [degree_2]
  decide

theorem atoms : source.atoms = {8,9,11} := by
  have he := Finset.insert_erase source.multiplicity_mem_atoms
  rw [← source.degree_one, degree_1, multiplicity] at he
  exact he.symm

theorem closure_generators : AddSubmonoid.closure ({8,9,11} : Set ℕ) = source.carrier := by
  rw [← source.closure_atoms, atoms]
  simp only [Finset.coe_insert, Finset.coe_singleton]

end evenMaximal
namespace rankThree

def allowed : Finset ℕ := {0,13,14,17,19,26,27,28,30,31,32,33,34,36}

def source : NumericalSemigroup where
  carrier :=
    { carrier := {n | n ∈ allowed ∨ 38 ≤ n}
      zero_mem' := Or.inl (by decide)
      add_mem' := by
        intro x y hx hy
        change x+y ∈ allowed ∨ 38 ≤ x+y
        change x ∈ allowed ∨ 38 ≤ x at hx
        change y ∈ allowed ∨ 38 ≤ y at hy
        simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
        omega }
  conductor := 38
  cofinite _ h := Or.inr h

theorem multiplicity : source.multiplicity = 13 := by
  apply source.multiplicity_eq (by decide) (Or.inl (by decide))
  intro n hn hp
  change n ∈ allowed ∨ 38 ≤ n at hn
  simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

def weight (n : ℕ) : ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,0,1,0,0,0,0,0,0,2,2,2,0,2,2,2,2,2,0,2,0,2,3,3,3,3,3,3,3,3,3,3,3,3][n]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem weight_step : ∀ x ∈ Finset.range 51, ∀ y ∈ Finset.range 51,
    (x ∈ allowed ∨ 38 ≤ x) → 0 < x → (y ∈ allowed ∨ 38 ≤ y) → x+y ≤ 50 →
      weight y+1 ≤ weight (x+y) := by decide

theorem order_le (n : ℕ) (hn : n ∈ source) (hb : n ≤ 50) : source.order n ≤ weight n := by
  apply Run12Fixtures.length_weight_bound source 50 weight ?_ (source.order_length hn) hb
  intro a ha hp b hB hab
  exact weight_step a (Finset.mem_range.mpr (by omega)) b (Finset.mem_range.mpr (by omega)) ha hp hB hab

theorem order_14 : source.order 14 = 1 := by
  have hu := order_le 14 (by change 14 ∈ allowed ∨ 38 ≤ 14; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 14 1 from
    ⟨![14], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_17 : source.order 17 = 1 := by
  have hu := order_le 17 (by change 17 ∈ allowed ∨ 38 ≤ 17; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 17 1 from
    ⟨![17], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_19 : source.order 19 = 1 := by
  have hu := order_le 19 (by change 19 ∈ allowed ∨ 38 ≤ 19; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 19 1 from
    ⟨![19], by
      intro i
      fin_cases i
      exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_28 : source.order 28 = 2 := by
  have hu := order_le 28 (by change 28 ∈ allowed ∨ 38 ≤ 28; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 28 2 from
    ⟨![14,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_31 : source.order 31 = 2 := by
  have hu := order_le 31 (by change 31 ∈ allowed ∨ 38 ≤ 31; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 31 2 from
    ⟨![17,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_33 : source.order 33 = 2 := by
  have hu := order_le 33 (by change 33 ∈ allowed ∨ 38 ≤ 33; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 33 2 from
    ⟨![19,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_34 : source.order 34 = 2 := by
  have hu := order_le 34 (by change 34 ∈ allowed ∨ 38 ≤ 34; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 34 2 from
    ⟨![17,17], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_36 : source.order 36 = 2 := by
  have hu := order_le 36 (by change 36 ∈ allowed ∨ 38 ≤ 36; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 36 2 from
    ⟨![19,17], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_38 : source.order 38 = 2 := by
  have hu := order_le 38 (by change 38 ∈ allowed ∨ 38 ≤ 38; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 38 2 from
    ⟨![19,19], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_42 : source.order 42 = 3 := by
  have hu := order_le 42 (by change 42 ∈ allowed ∨ 38 ≤ 42; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 42 3 from
    ⟨![14,14,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_48 : source.order 48 = 3 := by
  have hu := order_le 48 (by change 48 ∈ allowed ∨ 38 ≤ 48; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 48 3 from
    ⟨![17,17,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_50 : source.order 50 = 3 := by
  have hu := order_le 50 (by change 50 ∈ allowed ∨ 38 ≤ 50; decide) (by decide)
  norm_num [weight] at hu
  have hl := source.length_le_order (show source.HasLength 50 3 from
    ⟨![19,17,14], by
      intro i
      fin_cases i <;> exact ⟨by change _ ∈ allowed ∨ 38 ≤ _; decide, by decide⟩,
      by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem apery : source.aperySet = {0,14,17,19,28,31,33,34,36,38,42,48,50} := by
  have hs : ({0,14,17,19,28,31,33,34,36,38,42,48,50} : Finset ℕ) ⊆ source.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact source.zero_mem_apery
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 14 ∈ allowed ∨ 38 ≤ 14; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 17 ∈ allowed ∨ 38 ≤ 17; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 19 ∈ allowed ∨ 38 ≤ 19; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 28 ∈ allowed ∨ 38 ≤ 28; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 31 ∈ allowed ∨ 38 ≤ 31; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 33 ∈ allowed ∨ 38 ≤ 33; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 34 ∈ allowed ∨ 38 ≤ 34; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 36 ∈ allowed ∨ 38 ≤ 36; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 38 ∈ allowed ∨ 38 ≤ 38; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 42 ∈ allowed ∨ 38 ≤ 42; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 48 ∈ allowed ∨ 38 ≤ 48; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply (source.mem_aperySet_iff _).2
      refine ⟨by change 50 ∈ allowed ∨ 38 ≤ 50; decide, ?_⟩
      intro y hy hm
      change y ∈ allowed ∨ 38 ≤ y at hy
      rw [multiplicity] at hm
      simp only [allowed, Finset.mem_insert, Finset.mem_singleton] at hy
      omega
  symm
  apply Finset.eq_of_subset_of_card_le hs
  rw [source.apery_card, multiplicity]
  decide

theorem degree_1 : source.degreeSet 1 = {14,17,19} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_14, order_17, order_19, order_28, order_31, order_33, order_34, order_36, order_38, order_42, order_48, order_50]
  decide

theorem degree_2 : source.degreeSet 2 = {28,31,33,34,36,38} := by
  simp only [degreeSet, apery, Finset.filter_insert, Finset.filter_singleton,
    source.order_zero, order_14, order_17, order_19, order_28, order_31, order_33, order_34, order_36, order_38, order_42, order_48, order_50]
  decide

theorem embedding : source.embeddingDimension = 4 := by
  have hc := source.degree_one_card
  rw [degree_1] at hc
  norm_num at hc
  have := source.embeddingDimension_pos
  omega

theorem quadratic_dimension (k : Type*) [Field k] :
    Module.finrank k (source.qDegree k 2) = 6 := by
  rw [source.qDegree_finrank, degree_2]
  decide

theorem cut_rank : source.actualCutRank = 3 := by
  unfold actualCutRank
  rw [degree_2]
  decide

theorem atoms : source.atoms = {13,14,17,19} := by
  have he := Finset.insert_erase source.multiplicity_mem_atoms
  rw [← source.degree_one, degree_1, multiplicity] at he
  exact he.symm

theorem closure_generators : AddSubmonoid.closure ({13,14,17,19} : Set ℕ) = source.carrier := by
  rw [← source.closure_atoms, atoms]
  simp only [Finset.coe_insert, Finset.coe_singleton]

end rankThree

end Run14Fixtures
