module

public import NSP14.Semigroup.AperyQuotient

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def nonAperyMonomial (x : S.NonAperyHeadExponent) :
    (S.nonAperyIdeal k).restrictScalars k :=
  ⟨S.headMonomial k x.val.val, S.headMonomial_mem_nonAperySpace k _ x.property⟩

theorem nonAperyIdealEquiv_initial (x : S.NonAperyHeadExponent) :
    S.nonAperyIdealEquiv k (S.nonAperyMonomial k x) = Finsupp.single x 1 := by
  ext y
  change S.headQuotientEquiv k (S.headMonomial k x.val.val) y.val = Finsupp.single x (1 : k) y
  calc
    _ = Finsupp.single x.val.val (1 : k) y.val.val := S.headMonomial_coordinates k _ _
    _ = _ := by
      by_cases h : x = y
      · subst y; simp
      · have hv : x.val.val ≠ y.val.val := fun he => h (Subtype.ext (Subtype.ext he))
        simp [h, hv]

theorem nonAperyIdealBasis_eq_initial (x : S.NonAperyHeadExponent) :
    (S.nonAperyIdealBasis k x).val = S.headMonomial k x.val.val := by
  have he : S.nonAperyIdealBasis k x = S.nonAperyMonomial k x := by
    apply (S.nonAperyIdealEquiv k).injective
    rw [S.nonAperyIdealEquiv_initial]
    simp [nonAperyIdealBasis]
  exact congrArg Subtype.val he

theorem qMonomial_ne_zero_iff (x : S.carrier) :
    S.qMonomial k x ≠ 0 ↔ x.val ∈ S.aperySet := by
  constructor
  · intro h
    by_contra hx
    exact h (S.qMonomial_zero_of_nonapery k x hx)
  · intro hx
    exact S.qMonomial_ne_zero k ⟨x, hx⟩

theorem qMonomial_mul_nonapery (x y : S.carrier) (h : (x + y).val ∉ S.aperySet) :
    S.qMonomial k x * S.qMonomial k y = 0 := by
  by_cases hlive : S.order (x.val + y.val) = S.order x.val + S.order y.val
  · rw [S.qMonomial_mul_live k x y hlive]
    exact S.qMonomial_zero_of_nonapery k _ h
  · apply S.qMonomial_mul_dead
    have ho := S.order_add x.property y.property
    omega

theorem qMonomial_mul_ne_zero_iff (x y : S.carrier) :
    S.qMonomial k x * S.qMonomial k y ≠ 0 ↔
      S.order (x.val + y.val) = S.order x.val + S.order y.val ∧ (x + y).val ∈ S.aperySet := by
  by_cases hlive : S.order (x.val + y.val) = S.order x.val + S.order y.val
  · rw [S.qMonomial_mul_live k x y hlive, S.qMonomial_ne_zero_iff]
    exact ⟨fun h => ⟨hlive, h⟩, fun h => h.2⟩
  · have hdead : S.qMonomial k x * S.qMonomial k y = 0 := by
      apply S.qMonomial_mul_dead
      have ho := S.order_add x.property y.property
      omega
    simp only [hdead, ne_eq, not_true_eq_false, false_iff]
    exact fun h => hlive h.1

end NSP14.NumericalSemigroup
