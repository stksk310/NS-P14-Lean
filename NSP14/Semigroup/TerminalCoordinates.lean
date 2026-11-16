module

public import NSP14.Semigroup.PolynomialPresentation

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Reindex the actual non-Apéry head basis by its unique terminal predecessor. -/
noncomputable def terminalHeadExponentEquiv : S.TerminalExponent ≃ S.NonAperyHeadExponent where
  toFun t := ⟨⟨S.shiftExponent t.val, ((S.terminal_iff_head t.val.val).1 t.property).1⟩,
    ((S.terminal_iff_head t.val.val).1 t.property).2⟩
  invFun h := ⟨⟨h.val.val.val-S.multiplicity,(S.head_sub_terminal ⟨h.val.property,h.property⟩).1⟩,
    S.head_sub_terminal ⟨h.val.property,h.property⟩⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; simp [shiftExponent]
  right_inv h := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change h.val.val.val-S.multiplicity+S.multiplicity=h.val.val.val
    obtain ⟨t,_,he⟩ := S.head_predecessor ⟨h.val.property,h.property⟩
    omega

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- A k-linear coordinate equivalence only; no global S₀-linearity is claimed. -/
noncomputable def terminalHeadVectorEquiv :
    (S.xMultiply k).ker ≃ₗ[k] (S.nonAperyIdeal k).restrictScalars k :=
  (S.xKernelEquiv k).trans ((Finsupp.domLCongr (S.terminalHeadExponentEquiv)).trans
    (S.nonAperyIdealEquiv k).symm)

theorem terminal_head_degree_shift (t : S.TerminalExponent) :
    S.order (S.terminalHeadExponentEquiv t).val.val.val = S.order t.val.val + S.jump t.val.val := by
  change S.order (t.val.val+S.multiplicity) = S.order t.val.val +
    (S.order (t.val.val+S.multiplicity)-S.order t.val.val)
  have := S.order_add_multiplicity t.val.property
  omega

theorem terminal_head_degree_shift_of_jump (t : S.TerminalExponent) (s : ℕ)
    (h : S.jump t.val.val = s) :
    S.order (S.terminalHeadExponentEquiv t).val.val.val = S.order t.val.val + s := by
  rw [S.terminal_head_degree_shift, h]

theorem xKernel_eq_bot_of_deficit_zero (h : S.deficit = 0) : (S.xMultiply k).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have he : S.xKernelEquiv k ⟨a,ha⟩ = 0 := by
    ext t
    exact (S.no_terminal_of_deficit_zero h t.val.val t.property).elim
  have hh := (S.xKernelEquiv k).injective (he.trans (map_zero _).symm)
  exact congrArg Subtype.val hh

theorem nonAperyIdeal_eq_bot_of_deficit_zero (h : S.deficit = 0) : S.nonAperyIdeal k = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have he : S.nonAperyIdealEquiv k ⟨a,ha⟩ = 0 := by
    ext t
    have ht := (S.terminalHeadExponentEquiv).symm t
    exact (S.no_terminal_of_deficit_zero h ht.val.val ht.property).elim
  have hh := (S.nonAperyIdealEquiv k).injective (he.trans (map_zero _).symm)
  exact congrArg Subtype.val hh

end NSP14.NumericalSemigroup
