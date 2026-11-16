module
public import NSP14.ArithmeticSequence.MaximalEmbeddingBetti
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace ArithmeticSequenceMaximalBettiAcceptance

def D : ArithmeticSequence.Data where
  m := 5
  d := 2
  v := 4
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem actual_zero : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) 0=1 :=
  D.maximalEmbedding_betti_zero (ZMod 2) rfl

theorem actual_first : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) 1=10 := by
  rw [D.maximalEmbedding_betti (ZMod 2) rfl 1 (by decide)]
  decide

theorem actual_top : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) 4=4 := by
  rw [D.maximalEmbedding_betti (ZMod 2) rfl 4 (by decide)]
  decide

theorem actual_above : totalBetti (ZMod 2) D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing (ZMod 2)) (D.source.TangentAlgebra (ZMod 2))) 5=0 := by
  rw [D.maximalEmbedding_betti (ZMod 2) rfl 5 (by decide)]
  decide

def D2 : ArithmeticSequence.Data where
  m := 2
  d := 1
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem actual_two_variable_target : totalBetti (ZMod 2) D2.source.AtomExponent
    (ModuleCat.of (D2.source.FullPolynomialRing (ZMod 2)) (D2.source.TangentAlgebra (ZMod 2))) 1=1 := by
  rw [D2.maximalEmbedding_betti (ZMod 2) rfl 1 (by decide)]
  decide
end ArithmeticSequenceMaximalBettiAcceptance
