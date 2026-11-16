module

public import NSP14
public import tests.Run12Fixtures
public import tests.Run12BasicExamples

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup
open scoped Classical
local instance : Fact (1 < (4 : ℕ)) := ⟨by decide⟩

section Generic
variable (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]
example (s : ℕ) (hs : 0<s) :
    S.DescendingJumpStratum k s ≃ₗ[S.PolynomialRing k] S.AscendingJumpStratum k s := S.jumpStratumEquiv k s hs
example (s : ℕ) (hs : 0<s) (p : ℕ) (a : S.DescendingJumpStratum k s) :
    S.jumpStratumEquiv k s hs a ∈ S.ascendingStratumDegree k s (p+s) ↔ a ∈ S.descendingStratumDegree k s p :=
  S.jumpStratumEquiv_degree k s hs p a
example : S.descendingJump k 2 = ⊤ := S.descendingJump_two k
example : S.descendingJump k (S.qTopDegree+1)=⊥ := S.descendingJump_top_succ k
example : S.ascendingJump k 1 = ⊥ := S.ascendingJump_one k
example : S.ascendingJump k S.qTopDegree=⊤ := S.ascendingJump_top k
example (s p : ℕ) (a : S.descendingJump k s) :
    (⟨S.tangentGradeProject k p a.val.val,S.tangentGradeProject_mem_kernel k p a.val⟩ : (S.xMultiply k).ker)
      ∈ S.descendingJump k s := S.descendingJump_homogeneous k s p a
example (s p : ℕ) (a : S.ascendingJump k s) :
    (⟨S.headGradeProject k p a.val.val,S.headGradeProject_mem_nonAperyIdeal k p a.val.val a.val.property⟩ :
      (S.nonAperyIdeal k).restrictScalars k) ∈ S.ascendingJump k s := S.ascendingJump_homogeneous k s p a
end Generic

namespace JumpStrataExamples
open Run12Fixtures

noncomputable def atom15 : changing.NonXAtom :=
  ⟨v15,(changing.order_one_iff_atom v15.property).1 order_15,by rw [changing_m]; decide⟩
noncomputable def t26 : changing.TerminalExponent := ⟨v26,terminal_26⟩
noncomputable def t41 : changing.TerminalExponent := ⟨v41,terminal_41⟩
noncomputable def j26 : changing.JumpExponent 2 := ⟨t26,jump_26⟩
noncomputable def j41 : changing.JumpExponent 3 := ⟨t41,jump_41⟩

theorem base_action_live (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom15 : changing.PolynomialRing k) • changing.terminalMonomial k t26 =
      changing.terminalMonomial k t41 := by
  apply Subtype.ext
  change changing.polynomialToG k (MvPolynomial.X atom15)*changing.initialMonomial k v26 = _
  rw [changing.polynomialToG_X]
  have hl : changing.order (v15.val+v26.val) = changing.order v15.val+changing.order v26.val := by
    change changing.order 41=changing.order 15+changing.order 26
    rw [order_41,order_15,order_26]
  exact changing.initialMonomial_mul_live k v15 v26 hl

/-- A live T action raises jump 2→3 and therefore disappears in the jump-2 quotient. -/
theorem changed_jump_vanishes (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom15 : changing.PolynomialRing k) •
      (Submodule.Quotient.mk (changing.descendingJumpMonomial k 2 j26) : changing.DescendingJumpStratum k 2)=0 := by
  change (Submodule.Quotient.mk ((MvPolynomial.X atom15 : changing.PolynomialRing k) •
    changing.descendingJumpMonomial k 2 j26) : changing.DescendingJumpStratum k 2)=0
  rw [Submodule.Quotient.mk_eq_zero]
  change (MvPolynomial.X atom15 : changing.PolynomialRing k) • changing.terminalMonomial k t26 ∈ changing.descendingJump k 3
  rw [base_action_live]
  exact changing.initial_mem_jumpGSpace k 3 v41 terminal_41 (le_of_eq jump_41.symm)

example : changing.jump 26 < changing.jump 41 := by rw [jump_26,jump_41]; decide

example : (Submodule.Quotient.mk (changing.descendingJumpMonomial ℚ 2 j26) : changing.DescendingJumpStratum ℚ 2) ≠ 0 := by
  intro h
  have hh := congrArg (changing.descendingStratumCoordinates ℚ 2) h
  rw [changing.descendingJumpMonomial_coordinates,map_zero] at hh
  exact Finsupp.single_ne_zero.mpr one_ne_zero hh

example : (Submodule.Quotient.mk (changing.ascendingJumpMonomial (ZMod 2) 3 j41) : changing.AscendingJumpStratum (ZMod 2) 3) ≠ 0 := by
  intro h
  have hh := congrArg (changing.ascendingStratumCoordinates (ZMod 2) 3 (by decide)) h
  rw [changing.ascendingJumpMonomial_coordinates,map_zero] at hh
  exact Finsupp.single_ne_zero.mpr one_ne_zero hh

example : (MvPolynomial.X atom15 : changing.PolynomialRing (ZMod 4)) •
    (Submodule.Quotient.mk (changing.descendingJumpMonomial (ZMod 4) 2 j26) : changing.DescendingJumpStratum (ZMod 4) 2)=0 :=
  changed_jump_vanishes (ZMod 4)

/-- The same action vanishes in the matched N stratum by the proved S₀-linearity. -/
example : (MvPolynomial.X atom15 : changing.PolynomialRing ℚ) •
    changing.jumpStratumEquiv ℚ 2 (by decide)
      (Submodule.Quotient.mk (changing.descendingJumpMonomial ℚ 2 j26)) = 0 := by
  rw [← map_smul,changed_jump_vanishes,map_zero]

end JumpStrataExamples

namespace JumpStrataBoundary
open AperyQuotientExamples

theorem singular_top : singular.qTopDegree=2 := by
  norm_num [qTopDegree,singular_apery,singular.order_zero,order_five,order_ten,order_eleven]

noncomputable def singularTerminal : singular.TerminalExponent := ⟨v11,by
  refine ⟨v11.property,?_⟩
  change singular.order 11+1<singular.order (11+singular.multiplicity)
  rw [singular_m,order_eleven]
  change 2<singular.order 15
  rw [order_fifteen]; decide⟩

noncomputable def singularJump : singular.JumpExponent singular.qTopDegree := ⟨singularTerminal,by
  change singular.order (11+singular.multiplicity)-singular.order 11=singular.qTopDegree
  rw [singular_m,order_eleven,singular_top]
  change singular.order 15-1=2
  rw [order_fifteen]⟩

example : (Submodule.Quotient.mk (singular.descendingJumpMonomial ℚ singular.qTopDegree singularJump) :
    singular.DescendingJumpStratum ℚ singular.qTopDegree)≠0 := by
  intro h
  have hh := congrArg (singular.descendingStratumCoordinates ℚ singular.qTopDegree) h
  rw [singular.descendingJumpMonomial_coordinates,map_zero] at hh
  exact Finsupp.single_ne_zero.mpr one_ne_zero hh
end JumpStrataBoundary
