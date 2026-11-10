module
public import NSP14.ArithmeticSequence.ConeBetti
public import tests.ArithmeticSequenceMaximalBetti
@[expose] public section
open NSP14 NSP14.Homological
namespace ArithmeticSequenceConeBettiAcceptance

/-- All fields, all rows, actual rings and their full minimal presentations. -/
theorem genuine_general_comparison (D : ArithmeticSequence.Data) (k : Type) [Field k] (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i :=
  D.semigroup_cone_totalBetti k i

def mixed : ArithmeticSequence.Data where
  m := 5
  d := 2
  v := 3
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

/-- A nonordinary, non-maximal-embedding AP in characteristic two. -/
theorem mixed_all_rows (i : ℕ) :
    totalBetti (ZMod 2) mixed.source.AtomExponent
      (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) i=
    totalBetti (ZMod 2) mixed.source.AtomExponent
      (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.TangentAlgebra (ZMod 2))) i :=
  mixed.semigroup_cone_totalBetti (ZMod 2) i

/-- Transfer the previously independently computed cone value to the
actual algebraic ring, using the new all-row comparison. -/
theorem algebraic_maximal_first :
    let D := ArithmeticSequenceMaximalBettiAcceptance.D
    totalBetti (ZMod 2) D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.SemigroupRing (ZMod 2))) 1=10 := by
  dsimp only
  rw [ArithmeticSequenceMaximalBettiAcceptance.D.semigroup_cone_totalBetti]
  exact ArithmeticSequenceMaximalBettiAcceptance.actual_first
end ArithmeticSequenceConeBettiAcceptance
