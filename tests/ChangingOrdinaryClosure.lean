module
public import NSP14.Ordinary.Closure
public import tests.Run12Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace ChangingOrdinaryClosureAcceptance
abbrev S := Run12Fixtures.changing

theorem atom_15 : 15∈S.atoms :=
  (S.mem_atoms_iff 15).mpr ((S.order_one_iff_atom Run12Fixtures.v15.property).mp Run12Fixtures.order_15)
theorem atom_26 : 26∈S.atoms :=
  (S.mem_atoms_iff 26).mpr ((S.order_one_iff_atom Run12Fixtures.v26.property).mp Run12Fixtures.order_26)

theorem embedding_lower : 3≤S.embeddingDimension := by
  have h9 : 9∈S.atoms := by rw [← Run12Fixtures.changing_m];exact S.multiplicity_mem_atoms
  have hs : ({9,15,26} : Finset ℕ)⊆S.atoms := by
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact h9
    · exact atom_15
    · exact atom_26
  have hc := Finset.card_le_card hs
  have h3 : ({9,15,26} : Finset ℕ).card=3 := by decide
  rw [h3] at hc
  exact hc

theorem source_wide : S.multiplicity-1≤S.width := by
  have hm := S.atom_le_maxAtom atom_26
  unfold NumericalSemigroup.width
  rw [Run12Fixtures.changing_m]
  omega

/-- The actual changing-jump fixture retains both nonzero terminals. -/
theorem actual_terminals : S.Terminal 26 ∧ S.Terminal 41 :=
  ⟨Run12Fixtures.terminal_26,Run12Fixtures.terminal_41⟩

theorem actual_completed_all_rows (i : ℕ) :
    let T := S.intervalCompletion (show 2≤S.embeddingDimension from by have := embedding_lower;omega)
    totalBetti (ZMod 2) S.AtomExponent (ModuleCat.of (S.FullPolynomialRing (ZMod 2)) (S.FormalTangentAlgebra (ZMod 2))) i ≤
      totalBetti (ZMod 2) T.AtomExponent (ModuleCat.of (T.FullPolynomialRing (ZMod 2)) (T.FormalTangentAlgebra (ZMod 2))) i :=
  Ordinary.ordinary_actual_completion_betti_le S (ZMod 2) embedding_lower source_wide i
end ChangingOrdinaryClosureAcceptance
