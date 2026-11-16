module
public import NSP14.Ordinary.Closure
public import NSP14.ArithmeticSequence.TwoGeneratorBetti
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace OrdinaryClosureAcceptance
abbrev S := Run14Fixtures.rankTwo.source

theorem source_wide : S.multiplicity-1≤S.width := by
  have ha : 11∈S.atoms := by rw [Run14Fixtures.rankTwo.atoms];decide
  have hm := S.atom_le_maxAtom ha
  unfold NumericalSemigroup.width
  rw [Run14Fixtures.rankTwo.multiplicity]
  omega

theorem actual_completed_all_rows (i : ℕ) :
    let T := S.intervalCompletion (by rw [Run14Fixtures.rankTwo.embedding];decide)
    totalBetti (ZMod 2) S.AtomExponent (ModuleCat.of (S.FullPolynomialRing (ZMod 2)) (S.FormalTangentAlgebra (ZMod 2))) i ≤
      totalBetti (ZMod 2) T.AtomExponent (ModuleCat.of (T.FullPolynomialRing (ZMod 2)) (T.FormalTangentAlgebra (ZMod 2))) i :=
  Ordinary.ordinary_actual_completion_betti_le S (ZMod 2) (by rw [Run14Fixtures.rankTwo.embedding]) source_wide i

theorem actual_completed_source_zero :
    totalBetti (ZMod 2) S.AtomExponent (ModuleCat.of (S.FullPolynomialRing (ZMod 2)) (S.FormalTangentAlgebra (ZMod 2))) 0=1 :=
  S.completed_totalBetti_zero (ZMod 2)

def D : ArithmeticSequence.Data where
  m := 3
  d := 2
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem genuine_d_two_betti_one : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) 1=1 :=
  D.twoGenerator_cone_betti_one (ZMod 2) rfl

theorem genuine_d_two_above (i : ℕ) (hi : 1 < i) : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) i=0 :=
  D.twoGenerator_cone_betti_above (ZMod 2) rfl i hi
end OrdinaryClosureAcceptance
