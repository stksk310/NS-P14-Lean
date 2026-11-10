module

public import NSP14

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup
open scoped Classical BigOperators

-- Numerical fixture definitions copied verbatim from the frozen Block11 test.
-- Kept in a public fixture module because the original test deliberately exports no API.
namespace AperyQuotientExamples

def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite _ _ := by trivial

theorem naturals_m : naturals.multiplicity = 1 :=
  naturals.multiplicity_eq (by decide) (by trivial) (by intro x _ hx; omega)

theorem naturals_e : naturals.embeddingDimension = 1 := by
  have hl := naturals.embeddingDimension_pos
  have hu := naturals.embeddingDimension_le_multiplicity
  rw [naturals_m] at hu
  omega

example : Module.finrank ℚ (naturals.AperyAlgebra ℚ) = 1 := by
  rw [naturals.aperyAlgebra_finrank, naturals_m]

example : Module.finrank ℚ (naturals.qDegree ℚ 1) = 0 := by
  rw [naturals.qDegree_one_finrank, naturals_e]

example : naturals.qDegree ℚ 2 = ⊥ := by
  apply naturals.qDegree_eq_bot_of_gt
  simp [deficit, naturals_m, naturals_e]

/-- A genuine singular example with a non-Apéry head in degree three. -/
def singular : NumericalSemigroup where
  carrier :=
    { carrier := {n | n=0 ∨ n=4 ∨ n=5 ∨ n=8 ∨ n=9 ∨ n=10 ∨ 11≤n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro x y hx hy
        change x+y=0 ∨ x+y=4 ∨ x+y=5 ∨ x+y=8 ∨ x+y=9 ∨ x+y=10 ∨ 11≤x+y
        change x=0 ∨ x=4 ∨ x=5 ∨ x=8 ∨ x=9 ∨ x=10 ∨ 11≤x at hx
        change y=0 ∨ y=4 ∨ y=5 ∨ y=8 ∨ y=9 ∨ y=10 ∨ 11≤y at hy
        omega }
  conductor := 11
  cofinite _ hn := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))

theorem singular_m : singular.multiplicity = 4 := by
  apply singular.multiplicity_eq (by decide) (show 4 ∈ singular from Or.inr (Or.inl rfl))
  intro x hx hp
  change x=0 ∨ x=4 ∨ x=5 ∨ x=8 ∨ x=9 ∨ x=10 ∨ 11≤x at hx
  omega

def v5 : singular.carrier := ⟨5, Or.inr (Or.inr (Or.inl rfl))⟩
def v10 : singular.carrier := ⟨10, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
def v11 : singular.carrier := ⟨11, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))⟩
def v15 : singular.carrier := ⟨15, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))⟩

theorem atom_five : singular.IsAtom 5 := by
  refine ⟨v5.property, by decide, ?_⟩
  intro u hu v hv heq
  change u=0 ∨ u=4 ∨ u=5 ∨ u=8 ∨ u=9 ∨ u=10 ∨ 11≤u at hu
  change v=0 ∨ v=4 ∨ v=5 ∨ v=8 ∨ v=9 ∨ v=10 ∨ 11≤v at hv
  omega

theorem atom_eleven : singular.IsAtom 11 := by
  refine ⟨v11.property, by decide, ?_⟩
  intro u hu v hv heq
  change u=0 ∨ u=4 ∨ u=5 ∨ u=8 ∨ u=9 ∨ u=10 ∨ 11≤u at hu
  change v=0 ∨ v=4 ∨ v=5 ∨ v=8 ∨ v=9 ∨ v=10 ∨ 11≤v at hv
  omega

theorem order_five : singular.order 5 = 1 := singular.atom_order atom_five
theorem order_eleven : singular.order 11 = 1 := singular.atom_order atom_eleven

theorem order_ten : singular.order 10 = 2 := by
  have hl := singular.length_le_order
    (show singular.HasLength 10 2 from ⟨fun _ => 5, fun _ => ⟨v5.property, by norm_num⟩, by norm_num⟩)
  have hu := singular.order_bound v10.property
  change singular.order 10 * singular.multiplicity ≤ 10 at hu
  rw [singular_m] at hu
  omega

theorem order_fifteen : singular.order 15 = 3 := by
  have hl := singular.length_le_order
    (show singular.HasLength 15 3 from ⟨fun _ => 5, fun _ => ⟨v5.property, by norm_num⟩, by norm_num⟩)
  have hu := singular.order_bound v15.property
  change singular.order 15 * singular.multiplicity ≤ 15 at hu
  rw [singular_m] at hu
  omega

theorem five_apery : 5 ∈ singular.aperySet := by
  rw [singular.mem_aperySet_iff, singular_m]
  refine ⟨v5.property, ?_⟩
  intro y hy hmod
  change y=0 ∨ y=4 ∨ y=5 ∨ y=8 ∨ y=9 ∨ y=10 ∨ 11≤y at hy
  omega

theorem ten_apery : 10 ∈ singular.aperySet := by
  rw [singular.mem_aperySet_iff, singular_m]
  refine ⟨v10.property, ?_⟩
  intro y hy hmod
  change y=0 ∨ y=4 ∨ y=5 ∨ y=8 ∨ y=9 ∨ y=10 ∨ 11≤y at hy
  omega

theorem eleven_apery : 11 ∈ singular.aperySet := by
  rw [singular.mem_aperySet_iff, singular_m]
  refine ⟨v11.property, ?_⟩
  intro y hy hmod
  change y=0 ∨ y=4 ∨ y=5 ∨ y=8 ∨ y=9 ∨ y=10 ∨ 11≤y at hy
  omega

theorem singular_apery : singular.aperySet = {0,5,10,11} := by
  have hsub : ({0,5,10,11} : Finset ℕ) ⊆ singular.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact singular.zero_mem_apery
    · exact five_apery
    · exact ten_apery
    · exact eleven_apery
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [singular.apery_card, singular_m]
  norm_num

theorem singular_degree_one : singular.degreeSet 1 = {5,11} := by
  simp only [degreeSet, singular_apery, Finset.filter_insert, Finset.filter_singleton,
    order_five, order_ten, order_eleven, singular.order_zero]
  norm_num

theorem singular_degree_two : singular.degreeSet 2 = {10} := by
  simp only [degreeSet, singular_apery, Finset.filter_insert, Finset.filter_singleton,
    order_five, order_ten, order_eleven, singular.order_zero]
  norm_num

theorem singular_e : singular.embeddingDimension = 3 := by
  have h := singular.degree_one_card
  rw [singular_degree_one] at h
  norm_num at h
  omega

theorem singular_delta : singular.deficit = 1 := by simp [deficit, singular_m, singular_e]

theorem fifteen_nonapery : 15 ∉ singular.aperySet := by
  rw [singular_apery]
  norm_num

theorem fifteen_head : singular.XHead 15 := by
  have ht : singular.Terminal 11 := by
    refine ⟨v11.property, ?_⟩
    rw [singular_m, order_eleven]
    change 1+1 < singular.order 15
    rw [order_fifteen]
    decide
  have hh := (singular.terminal_iff_head 11).1 ht
  simpa only [singular_m] using hh.1

theorem fifteen_in_N : singular.headMonomial ℚ v15 ∈ singular.nonAperyIdeal ℚ :=
  singular.headMonomial_mem_nonAperySpace ℚ v15 fifteen_nonapery

example : singular.headMonomial ℚ v15 ≠ 0 := singular.head_initial_ne_zero ℚ ⟨v15, fifteen_head⟩
example : singular.qMonomial ℚ v15 = 0 := singular.qMonomial_zero_of_nonapery ℚ v15 fifteen_nonapery
example (a : singular.HeadAlgebra ℚ) : a * singular.headMonomial ℚ v15 ∈ singular.nonAperyIdeal ℚ :=
  (singular.nonAperyIdeal ℚ).mul_mem_left a fifteen_in_N

example : Module.finrank ℚ (singular.AperyAlgebra ℚ) = 4 := by rw [singular.aperyAlgebra_finrank, singular_m]
example : Module.finrank ℚ (singular.qDegree ℚ 1) = 2 := by
  rw [singular.qDegree_finrank, singular_degree_one]
  norm_num
example : Module.finrank ℚ (singular.qDegree ℚ 2) = 1 := by
  rw [singular.qDegree_finrank, singular_degree_two]
  norm_num
example : singular.qDegree ℚ 3 = ⊥ := by
  apply singular.qDegree_eq_bot_of_gt
  rw [singular_delta]
  decide

example : singular.qMonomial ℚ v5 * singular.qMonomial ℚ v5 = singular.qMonomial ℚ v10 := by
  have hh : singular.order (v5.val+v5.val) = singular.order v5.val + singular.order v5.val := by
    change singular.order 10 = singular.order 5 + singular.order 5
    rw [order_ten, order_five]
  exact singular.qMonomial_mul_live ℚ v5 v5 hh

example : singular.qMonomial ℚ v10 ≠ 0 := singular.qMonomial_ne_zero ℚ ⟨v10, ten_apery⟩
example : singular.aperyAtomSubalgebra ℚ = ⊤ := singular.apery_atom_adjoin_top ℚ

example : singular.qTopDegree = 2 := by
  norm_num [qTopDegree, singular_apery, order_five, order_ten, order_eleven, singular.order_zero]

example : (singular.lowDegreeQuotientEquiv ℚ 2 le_rfl
    ⟨singular.headMonomial ℚ v10, singular.headMonomial_mem_degree ℚ v10 2 order_ten⟩).val =
    singular.qMonomial ℚ v10 := rfl

example (K : Type*) [Field K] : singular.qMonomial K v5 * singular.qMonomial K v11 = 0 := by
  apply singular.qMonomial_mul_nonapery
  change 16 ∉ singular.aperySet
  rw [singular_apery]
  norm_num

example (K : Type*) [Field K] : singular.qMonomial K v11 * singular.qMonomial K v11 = 0 := by
  apply singular.qMonomial_mul_nonapery
  change 22 ∉ singular.aperySet
  rw [singular_apery]
  norm_num

-- The ordinary semigroup with m=e=3 exercises δ=0 with a nonzero first degree.
def ordinaryThree : NumericalSemigroup where
  carrier :=
    { carrier := {n | n=0 ∨ 3≤n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro x y hx hy
        change x+y=0 ∨ 3≤x+y
        change x=0 ∨ 3≤x at hx
        change y=0 ∨ 3≤y at hy
        omega }
  conductor := 3
  cofinite _ hn := Or.inr hn

theorem ordinaryThree_m : ordinaryThree.multiplicity = 3 := by
  apply ordinaryThree.multiplicity_eq (by decide) (show 3 ∈ ordinaryThree from Or.inr (by decide))
  intro x hx hp
  change x=0 ∨ 3≤x at hx
  omega

theorem ordinaryThree_order_small (x : ℕ) (hx : 3≤x) (hmax : x<6) : ordinaryThree.order x = 1 := by
  have hm : x ∈ ordinaryThree := Or.inr hx
  have hl := ordinaryThree.order_pos hm (by omega)
  have hu := ordinaryThree.order_bound hm
  rw [ordinaryThree_m] at hu
  omega

theorem ordinaryThree_apery : ordinaryThree.aperySet = {0,4,5} := by
  have h4 : 4 ∈ ordinaryThree.aperySet := by
    rw [ordinaryThree.mem_aperySet_iff, ordinaryThree_m]
    refine ⟨Or.inr (by decide), ?_⟩
    intro y hy hmod
    change y=0 ∨ 3≤y at hy
    omega
  have h5 : 5 ∈ ordinaryThree.aperySet := by
    rw [ordinaryThree.mem_aperySet_iff, ordinaryThree_m]
    refine ⟨Or.inr (by decide), ?_⟩
    intro y hy hmod
    change y=0 ∨ 3≤y at hy
    omega
  have hs : ({0,4,5} : Finset ℕ) ⊆ ordinaryThree.aperySet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ordinaryThree.zero_mem_apery
    · exact h4
    · exact h5
  symm
  apply Finset.eq_of_subset_of_card_le hs
  rw [ordinaryThree.apery_card, ordinaryThree_m]
  norm_num

theorem ordinaryThree_degree_one : ordinaryThree.degreeSet 1 = {4,5} := by
  have h4 := ordinaryThree_order_small 4 (by decide) (by decide)
  have h5 := ordinaryThree_order_small 5 (by decide) (by decide)
  simp only [degreeSet, ordinaryThree_apery, Finset.filter_insert, Finset.filter_singleton,
    h4, h5, ordinaryThree.order_zero]
  norm_num

theorem ordinaryThree_e : ordinaryThree.embeddingDimension = 3 := by
  have h := ordinaryThree.degree_one_card
  rw [ordinaryThree_degree_one] at h
  norm_num at h
  omega

example : ordinaryThree.deficit = 0 := by simp [deficit, ordinaryThree_m, ordinaryThree_e]
example : Module.finrank ℚ (ordinaryThree.AperyAlgebra ℚ) = 3 := by
  rw [ordinaryThree.aperyAlgebra_finrank, ordinaryThree_m]
example : Module.finrank ℚ (ordinaryThree.qDegree ℚ 1) = 2 := by
  rw [ordinaryThree.qDegree_one_finrank, ordinaryThree_e]
example : ordinaryThree.qDegree ℚ 2 = ⊥ := by
  apply ordinaryThree.qDegree_eq_bot_of_gt
  simp [deficit, ordinaryThree_m, ordinaryThree_e]
example : ordinaryThree.qTopDegree = 1 := by
  have h4 := ordinaryThree_order_small 4 (by decide) (by decide)
  have h5 := ordinaryThree_order_small 5 (by decide) (by decide)
  norm_num [qTopDegree, ordinaryThree_apery, h4, h5, ordinaryThree.order_zero]

end AperyQuotientExamples
