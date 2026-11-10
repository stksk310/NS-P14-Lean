module

public import NSP14.Semigroup.LowDegreeQuotient
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

noncomputable def aperyExponentEquivSet : S.AperyExponent ≃ ↥S.aperySet where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, ((S.mem_aperySet_iff _).1 x.property).1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance aperyExponentFintype : Fintype S.AperyExponent :=
  Fintype.ofEquiv ↥S.aperySet S.aperyExponentEquivSet.symm

theorem aperyExponent_card : Fintype.card S.AperyExponent = S.multiplicity := by
  rw [Fintype.card_congr S.aperyExponentEquivSet, Fintype.card_coe, S.apery_card]

noncomputable def aperyDegreeEquivSet (n : ℕ) : S.AperyDegreeExponent n ≃ ↥(S.degreeSet n) where
  toFun x := ⟨x.val.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
  invFun x :=
    ⟨⟨⟨x.val, ((S.mem_aperySet_iff _).1 (Finset.mem_filter.mp x.property).1).1⟩,
      (Finset.mem_filter.mp x.property).1⟩, (Finset.mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance aperyDegreeExponentFintype (n : ℕ) : Fintype (S.AperyDegreeExponent n) :=
  Fintype.ofEquiv ↥(S.degreeSet n) (S.aperyDegreeEquivSet n).symm

theorem aperyDegreeExponent_card (n : ℕ) :
    Fintype.card (S.AperyDegreeExponent n) = (S.degreeSet n).card := by
  rw [Fintype.card_congr (S.aperyDegreeEquivSet n), Fintype.card_coe]

variable (k : Type*) [Field k]

noncomputable instance aperyAlgebraFinite : Module.Finite k (S.AperyAlgebra k) :=
  Module.Finite.of_basis (S.aperyQuotientBasis k)

/-- The dimension of the actual quotient Q=A/N is m. -/
theorem aperyAlgebra_finrank : Module.finrank k (S.AperyAlgebra k) = S.multiplicity := by
  rw [Module.finrank_eq_card_basis (S.aperyQuotientBasis k), S.aperyExponent_card]

noncomputable instance qDegreeFinite (n : ℕ) : Module.Finite k (S.qDegree k n) :=
  Module.Finite.of_basis (S.qDegreeBasis k n)

/-- The Hilbert function of the inherited quotient degree equals the actual Apéry count. -/
theorem qDegree_finrank (n : ℕ) : Module.finrank k (S.qDegree k n) = (S.degreeSet n).card := by
  rw [Module.finrank_eq_card_basis (S.qDegreeBasis k n), S.aperyDegreeExponent_card]

theorem qDegree_zero_finrank : Module.finrank k (S.qDegree k 0) = 1 := by
  rw [S.qDegree_finrank, S.degree_zero_card]

theorem qDegree_one_finrank : Module.finrank k (S.qDegree k 1) = S.embeddingDimension - 1 := by
  rw [S.qDegree_finrank, S.degree_one_card]

theorem qDegree_two_finrank_le : Module.finrank k (S.qDegree k 2) ≤ S.deficit := by
  rw [S.qDegree_finrank]
  exact S.degree_two_le_deficit

theorem qDegree_eq_bot_of_gt (n : ℕ) (hn : S.deficit + 1 < n) : S.qDegree k n = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply (S.aperyQuotientEquiv k).injective
  ext x
  have hbound := S.apery_order_bound x.property
  have hne : S.order x.val.val ≠ n := by omega
  exact (Finsupp.mem_supported' k _).1 ((S.mem_qDegree_coordinates k n a).1 ha) x hne

/-- The finite sum represents all degrees at least two, since higher pieces vanish. -/
theorem qDegree_high_sum :
    ∑ n ∈ Finset.Icc 2 (S.deficit + 1), Module.finrank k (S.qDegree k n) = S.deficit := by
  have h := Finset.card_eq_sum_card_fiberwise (f := S.order) (s := S.highSet)
    (t := Finset.Icc 2 (S.deficit + 1)) (fun x hx => by
      obtain ⟨ha, ho⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨ho, S.apery_order_bound ha⟩)
  rw [S.highSet_card] at h
  calc
    _ = ∑ n ∈ Finset.Icc 2 (S.deficit + 1), (S.highSet.filter (fun x => S.order x = n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [S.qDegree_finrank]
      congr 1
      ext x
      have hn2 := (Finset.mem_Icc.mp hn).1
      simp only [degreeSet, highSet, Finset.mem_filter]
      constructor
      · rintro ⟨ha, ho⟩
        exact ⟨⟨ha, ho.symm ▸ hn2⟩, ho⟩
      · rintro ⟨⟨ha, _⟩, ho⟩
        exact ⟨ha, ho⟩
    _ = _ := h.symm

theorem headDegree_low_finrank (n : ℕ) (hn : n ≤ 2) :
    Module.finrank k (S.headDegree k n) = (S.degreeSet n).card :=
  (S.lowDegreeQuotientEquiv k n hn).finrank_eq.trans (S.qDegree_finrank k n)

theorem headDegree_two_finrank_le : Module.finrank k (S.headDegree k 2) ≤ S.deficit := by
  rw [S.headDegree_low_finrank k 2 le_rfl]
  exact S.degree_two_le_deficit

end NSP14.NumericalSemigroup
