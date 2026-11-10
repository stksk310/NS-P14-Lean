module
public import NSP14.Target.IntervalAPBetti
public import NSP14.ArithmeticSequence.Width
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace IntervalAPBettiAcceptance

def narrow : ArithmeticSequence.Data where
  m := 5
  d := 1
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem narrow_embedding : 2 ≤ narrow.source.embeddingDimension := by
  rw [narrow.embeddingDimension]
  decide

theorem narrow_width : narrow.source.width=2 := by
  rw [narrow.width]
  rfl

/-- Literal completion of an actual width-2 source, with its own actual
minimal atoms, rather than an ordinary or virtual numerical target. -/
theorem literal_narrow_target_first :
    let T := narrow.source.intervalCompletion narrow_embedding
    totalBetti (ZMod 2) T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing (ZMod 2)) (T.FormalTangentAlgebra (ZMod 2))) 1=3 := by
  dsimp only
  rw [narrow.source.interval_completed_betti_profile (ZMod 2) narrow_embedding 1 (by decide)]
  simp only [ArithmeticSequence.Data.positiveBettiProfile,ArithmeticSequence.Data.residueDefect,
    NumericalSemigroup.intervalAP,ArithmeticSequence.intervalData]
  simp only [narrow_width,narrow.multiplicity]
  decide

theorem lower_profile_width_monotone (v w i : ℕ) (h : v≤w) :
    Target.apLowerProfile v i≤Target.apLowerProfile w i :=
  Target.apLowerProfile_monotone i h
end IntervalAPBettiAcceptance
