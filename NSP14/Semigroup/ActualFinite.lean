module

public import NSP14.Semigroup.OffsetStabilization
public import NSP14.Semigroup.TerminalCoordinates
public import NSP14.Semigroup.AperyDimensions

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Actual terminal labels are finite before any finrank is evaluated. -/
noncomputable instance terminalExponentFintype : Fintype S.TerminalExponent := by
  let f : S.TerminalExponent → Fin S.stabilizationBound :=
    fun x => ⟨x.val.val, S.terminal_lt_stabilizationBound x.property⟩
  exact Fintype.ofInjective f (fun x y h =>
    Subtype.ext (Subtype.ext (congrArg Fin.val h)))

noncomputable instance nonAperyHeadExponentFintype : Fintype S.NonAperyHeadExponent :=
  Fintype.ofEquiv S.TerminalExponent S.terminalHeadExponentEquiv

/-- Splitting the head basis keeps the actual Apéry and actual successor labels. -/
noncomputable def headExponentEquiv :
    S.HeadExponent ≃ S.AperyExponent ⊕ S.NonAperyHeadExponent where
  toFun x := if h : x.val.val ∈ S.aperySet then Sum.inl ⟨x.val, h⟩ else Sum.inr ⟨x, h⟩
  invFun x := match x with
    | Sum.inl a => ⟨a.val, S.apery_head a.property⟩
    | Sum.inr a => a.val
  left_inv x := by
    by_cases h : x.val.val ∈ S.aperySet
    · simp only [dite_eq_left h]
      exact Subtype.ext rfl
    · simp only [dite_eq_right h]
  right_inv x := by
    cases x with
    | inl a =>
      simp only [dite_eq_left a.property]
      exact congrArg Sum.inl (Subtype.ext rfl)
    | inr a =>
      simp only [dite_eq_right a.property]
      exact congrArg Sum.inr (Subtype.ext rfl)

noncomputable instance headExponentFintype : Fintype S.HeadExponent :=
  Fintype.ofEquiv (S.AperyExponent ⊕ S.NonAperyHeadExponent) S.headExponentEquiv.symm

theorem nonAperyHeadExponent_card :
    Fintype.card S.NonAperyHeadExponent = Fintype.card S.TerminalExponent :=
  Fintype.card_congr S.terminalHeadExponentEquiv.symm

theorem headExponent_card :
    Fintype.card S.HeadExponent = S.multiplicity + Fintype.card S.TerminalExponent := by
  rw [Fintype.card_congr S.headExponentEquiv, Fintype.card_sum,
    S.aperyExponent_card, S.nonAperyHeadExponent_card]

variable (k : Type*) [CommRing k] [Nontrivial k]

noncomputable instance terminalFinite : Module.Finite k ((S.xMultiply k).ker) :=
  Module.Finite.of_basis (S.xKernelBasis k)

noncomputable instance nonAperyFinite : Module.Finite k ((S.nonAperyIdeal k).restrictScalars k) :=
  Module.Finite.of_basis (S.nonAperyIdealBasis k)

noncomputable instance headAlgebraFinite : Module.Finite k (S.HeadAlgebra k) :=
  Module.Finite.of_basis (S.headBasis k)

section Field
variable (K : Type*) [Field K]

theorem terminal_finrank :
    Module.finrank K ((S.xMultiply K).ker) = Fintype.card S.TerminalExponent :=
  Module.finrank_eq_card_basis (S.xKernelBasis K)

theorem nonApery_finrank :
    Module.finrank K ((S.nonAperyIdeal K).restrictScalars K) = Fintype.card S.TerminalExponent := by
  rw [Module.finrank_eq_card_basis (S.nonAperyIdealBasis K), S.nonAperyHeadExponent_card]

theorem headAlgebra_finrank :
    Module.finrank K (S.HeadAlgebra K) = S.multiplicity + Fintype.card S.TerminalExponent := by
  rw [Module.finrank_eq_card_basis (S.headBasis K), S.headExponent_card]

/-- Dimension additivity now concerns genuine finite-dimensional spaces. -/
theorem headAlgebra_finrank_split :
    Module.finrank K (S.HeadAlgebra K) =
      Module.finrank K (S.AperyAlgebra K) +
        Module.finrank K ((S.nonAperyIdeal K).restrictScalars K) := by
  rw [S.headAlgebra_finrank, S.aperyAlgebra_finrank, S.nonApery_finrank]

end Field
end NSP14.NumericalSemigroup
