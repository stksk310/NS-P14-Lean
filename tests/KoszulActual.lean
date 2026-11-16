module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Actual
open NSP14.Homological CategoryTheory
open AperyQuotientExamples PolynomialExamples Run12Fixtures

theorem naturals_full_variables : Fintype.card naturals.AtomExponent=1 := by
  rw [naturals.atomExponent_card,naturals_e]
theorem naturals_nonx_variables : Fintype.card naturals.NonXAtom=0 := by
  rw [naturals.nonXAtom_card,naturals_e]
theorem two_full_variables : Fintype.card two.AtomExponent=2 := by rw [two.atomExponent_card,two_e]
theorem two_nonx_variables : Fintype.card two.NonXAtom=1 := by rw [two.nonXAtom_card,two_e]
noncomputable def naturals_completed_tor (i : ℕ) := naturals.completedTorIso ℚ i
noncomputable def two_completed_tor (i : ℕ) := two.completedTorIso (ZMod 2) i
noncomputable def changing_completed_tor (i : ℕ) := changing.completedTorIso ℚ i
noncomputable def changing_jump_two_tor (i : ℕ) := changing.jumpStratumTorIso (ZMod 2) 2 (by decide) i
noncomputable def changing_jump_three_tor (i : ℕ) := changing.jumpStratumTorIso ℚ 3 (by decide) i

theorem changing_completed_betti (i : ℕ) :
    totalBetti ℚ changing.AtomExponent (ModuleCat.of (changing.FullPolynomialRing ℚ) (changing.TangentAlgebra ℚ)) i =
      totalBetti ℚ changing.AtomExponent (ModuleCat.of (changing.FullPolynomialRing ℚ) (changing.FormalTangentAlgebra ℚ)) i :=
  changing.completed_totalBetti ℚ i

theorem changing_same_jump_betti (i : ℕ) :
    totalBetti (ZMod 2) changing.NonXAtom
      (ModuleCat.of (changing.PolynomialRing (ZMod 2)) (changing.DescendingJumpStratum (ZMod 2) 2)) i =
    totalBetti (ZMod 2) changing.NonXAtom
      (ModuleCat.of (changing.PolynomialRing (ZMod 2)) (changing.AscendingJumpStratum (ZMod 2) 2)) i :=
  changing.jumpStratum_totalBetti (ZMod 2) 2 (by decide) i

end Run13Actual
