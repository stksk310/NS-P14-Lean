module
public import NSP14.ArithmeticSequence.BettiFormula
public import NSP14.ArithmeticSequence.ProfileBounds
public import tests.ArithmeticSequenceConeBetti
@[expose] public section
open NSP14 NSP14.Homological
namespace ArithmeticSequenceBettiAcceptance

/-- The final export has no field, difference, row or endpoint restriction
beyond the original genuine minimal AP data. -/
theorem arbitrary_field_all_rows (D : ArithmeticSequence.Data) (k : Type) [Field k] (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=D.bettiProfile i :=
  D.semigroup_totalBetti k i

abbrev mixed := ArithmeticSequenceConeBettiAcceptance.mixed

theorem mixed_zero : totalBetti (ZMod 2) mixed.source.AtomExponent
    (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) 0=1 :=
  mixed.semigroup_totalBetti_zero (ZMod 2)

theorem mixed_first : totalBetti (ZMod 2) mixed.source.AtomExponent
    (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) 1=5 := by
  rw [mixed.semigroup_totalBetti_pos (ZMod 2) 1 (by decide)]
  decide

theorem mixed_at_D : totalBetti (ZMod 2) mixed.source.AtomExponent
    (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) 2=5 := by
  rw [mixed.semigroup_totalBetti_pos (ZMod 2) 2 (by decide)]
  decide

theorem mixed_at_D_succ_top : totalBetti (ZMod 2) mixed.source.AtomExponent
    (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) 3=1 := by
  rw [mixed.semigroup_totalBetti_pos (ZMod 2) 3 (by decide)]
  decide

theorem mixed_above : totalBetti (ZMod 2) mixed.source.AtomExponent
    (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.SemigroupRing (ZMod 2))) 4=0 :=
  mixed.semigroup_totalBetti_above (ZMod 2) 4 (by decide)

def endpoint_one : ArithmeticSequence.Data where
  m := 4
  d := 3
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem endpoint_one_first : totalBetti (ZMod 2) endpoint_one.source.AtomExponent
    (ModuleCat.of (endpoint_one.source.FullPolynomialRing (ZMod 2)) (endpoint_one.source.SemigroupRing (ZMod 2))) 1=2 := by
  rw [endpoint_one.semigroup_totalBetti_pos (ZMod 2) 1 (by decide)]
  decide

theorem endpoint_one_top : totalBetti (ZMod 2) endpoint_one.source.AtomExponent
    (ModuleCat.of (endpoint_one.source.FullPolynomialRing (ZMod 2)) (endpoint_one.source.SemigroupRing (ZMod 2))) 2=1 := by
  rw [endpoint_one.semigroup_totalBetti_pos (ZMod 2) 2 (by decide)]
  decide

def endpoint_v : ArithmeticSequence.Data where
  m := 5
  d := 2
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem endpoint_v_first : totalBetti (ZMod 2) endpoint_v.source.AtomExponent
    (ModuleCat.of (endpoint_v.source.FullPolynomialRing (ZMod 2)) (endpoint_v.source.SemigroupRing (ZMod 2))) 1=3 := by
  rw [endpoint_v.semigroup_totalBetti_pos (ZMod 2) 1 (by decide)]
  decide

theorem endpoint_v_top : totalBetti (ZMod 2) endpoint_v.source.AtomExponent
    (ModuleCat.of (endpoint_v.source.FullPolynomialRing (ZMod 2)) (endpoint_v.source.SemigroupRing (ZMod 2))) 2=2 := by
  rw [endpoint_v.semigroup_totalBetti_pos (ZMod 2) 2 (by decide)]
  decide

def two_gen : ArithmeticSequence.Data where
  m := 3
  d := 2
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem two_gen_first : totalBetti (ZMod 2) two_gen.source.AtomExponent
    (ModuleCat.of (two_gen.source.FullPolynomialRing (ZMod 2)) (two_gen.source.SemigroupRing (ZMod 2))) 1=1 := by
  rw [two_gen.semigroup_totalBetti_pos (ZMod 2) 1 (by decide)]
  decide

theorem completed_all_rows (i : ℕ) :
    totalBetti (ZMod 2) mixed.source.AtomExponent
      (ModuleCat.of (mixed.source.FullPolynomialRing (ZMod 2)) (mixed.source.FormalTangentAlgebra (ZMod 2))) i=mixed.bettiProfile i :=
  mixed.completed_AP_totalBetti (ZMod 2) i
end ArithmeticSequenceBettiAcceptance
