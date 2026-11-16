module
public import NSP14
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological NSP14.NumericalSemigroup
namespace RelativeXAcceptance
abbrev L := InfiniteScalarField (ZMod 2)
noncomputable def W : Ordinary.ActualWitness (ZMod 2) :=
  Ordinary.canonicalActualWitness Run14Fixtures.rankTwo.source (ZMod 2)
    (by rw [Run14Fixtures.rankTwo.embedding])

theorem actual_first_x (j : ℕ) :
    letI := W.relativeG_finite
    bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) ≤
      W.cut.cutAEuler (j+1)+W.cut.cutTEuler j := W.relative_Euler_le j

/-- Characteristic two, actual Gamma=<6,7,11>, terminal is r+1=3.
There is deliberately no assertion that c_2 over R vanishes. -/
theorem actual_terminal :
    letI := W.relativeG_finite
    bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG (2+1)=0 := by
  have h := W.relative_Euler_terminal
  have hr : W.source.actualCutRank=2 := Run14Fixtures.rankTwo.cut_rank
  simpa only [hr] using h

theorem actual_P_endpoints (j : ℕ) (hj : W.source.actualCutRank ≤ j) :
    W.cut.cutAEuler j=0 ∧ W.cut.cutTEuler j=0 :=
  ⟨W.cut.cutAEuler_eq_zero_of_ge j hj,W.cut.cutTEuler_eq_zero_of_ge j hj⟩
end RelativeXAcceptance
