module

public import NSP14.Semigroup.AperyGradedAlgebra

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- The largest numerical Apéry order, later identified with the actual top degree of Q. -/
noncomputable def qTopDegree : ℕ := S.aperySet.sup S.order

theorem qTopDegree_realized : ∃ x : S.AperyExponent, S.order x.val.val = S.qTopDegree := by
  obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_sup S.aperySet ⟨0, S.zero_mem_apery⟩ S.order
  exact ⟨⟨⟨x, ((S.mem_aperySet_iff x).1 hx).1⟩, hx⟩, heq.symm⟩

theorem apery_order_le_top (x : S.AperyExponent) : S.order x.val.val ≤ S.qTopDegree :=
  Finset.le_sup x.property

theorem qTopDegree_le_deficit : S.qTopDegree ≤ S.deficit + 1 :=
  Finset.sup_le (fun _ hx => S.apery_order_bound hx)

variable (k : Type*) [CommRing k] [Nontrivial k]

theorem qDegree_eq_bot_of_top_lt (n : ℕ) (hn : S.qTopDegree < n) : S.qDegree k n = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply (S.aperyQuotientEquiv k).injective
  ext x
  have hbound := S.apery_order_le_top x
  have hne : S.order x.val.val ≠ n := by omega
  exact (Finsupp.mem_supported' k _).1 ((S.mem_qDegree_coordinates k n a).1 ha) x hne

/-- There are no missing degrees up to the actual maximum. -/
theorem qDegree_ne_bot_iff (n : ℕ) : S.qDegree k n ≠ ⊥ ↔ n ≤ S.qTopDegree := by
  constructor
  · intro h
    by_contra hn
    exact h (S.qDegree_eq_bot_of_top_lt k n (by omega))
  · intro hn hb
    obtain ⟨w, hw⟩ := S.qTopDegree_realized
    obtain ⟨v, hv, ho⟩ := S.degree_exists_le w.property n (by omega)
    let x : S.AperyExponent := ⟨⟨v, ((S.mem_aperySet_iff v).1 hv).1⟩, hv⟩
    have hm := S.qMonomial_mem_degree k x.val n ho
    rw [hb] at hm
    exact S.qMonomial_ne_zero k x hm

theorem qDegree_top_ne_bot : S.qDegree k S.qTopDegree ≠ ⊥ := (S.qDegree_ne_bot_iff k _).2 le_rfl

end NSP14.NumericalSemigroup
