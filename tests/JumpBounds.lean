module

public import NSP14
public import tests.Run12Fixtures
public import tests.Run12BasicExamples

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup

example (S : NumericalSemigroup) {t : ℕ} (ht : S.Terminal t) : 2≤S.jump t ∧ S.jump t≤S.qTopDegree := S.terminal_jump_bounds ht
example (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k] (h : S.deficit=0) : (S.xMultiply k).ker=⊥ := S.xKernel_eq_bot_of_deficit_zero k h
example (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k] (h : S.deficit=0) : S.nonAperyIdeal k=⊥ := S.nonAperyIdeal_eq_bot_of_deficit_zero k h

open AperyQuotientExamples
example : (naturals.xMultiply ℚ).ker=⊥ := naturals.xKernel_eq_bot_of_deficit_zero ℚ (by simp [deficit,naturals_m,naturals_e])
example : ordinaryThree.nonAperyIdeal (ZMod 2)=⊥ := ordinaryThree.nonAperyIdeal_eq_bot_of_deficit_zero (ZMod 2)
  (by simp [deficit,ordinaryThree_m,ordinaryThree_e])
example : 2≤Run12Fixtures.changing.qTopDegree := by
  have h := Run12Fixtures.changing.terminal_jump_bounds Run12Fixtures.terminal_26
  rw [Run12Fixtures.jump_26] at h
  exact h.2
