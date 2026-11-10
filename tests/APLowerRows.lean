module
public import NSP14.Target.APLowerRows
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14 NSP14.Homological
namespace APLowerRowsAcceptance

theorem odd_three : Target.apLowerProfile 3 2=2*(3 : ℕ).choose 3+3 := by decide

theorem odd_five : Target.apLowerProfile 5 3=3*(5 : ℕ).choose 4+(5 : ℕ).choose 2 := by decide

def three : ArithmeticSequence.Data where
  m := 6
  d := 1
  v := 3
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

def five : ArithmeticSequence.Data where
  m := 8
  d := 1
  v := 5
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

/-- Nontrivial odd-endpoint equality in the actual quotient table,
in characteristic two, rather than just a virtual numerical profile. -/
theorem three_actual_second :
    totalBetti (ZMod 2) three.source.AtomExponent
      (ModuleCat.of (three.source.FullPolynomialRing (ZMod 2)) (three.source.SemigroupRing (ZMod 2))) 2=5 := by
  rw [three.semigroup_totalBetti_pos (ZMod 2) 2 (by decide)]
  decide

theorem five_actual_third :
    totalBetti (ZMod 2) five.source.AtomExponent
      (ModuleCat.of (five.source.FullPolynomialRing (ZMod 2)) (five.source.SemigroupRing (ZMod 2))) 3=25 := by
  rw [five.semigroup_totalBetti_pos (ZMod 2) 3 (by decide)]
  decide

/-- All four rows really specialize to a literal completed interval
with its own minimal variables, even at the conditional row endpoints. -/
theorem literal_target (S : NumericalSemigroup) (he : 2 ≤ S.embeddingDimension) :
    let v := min S.width (S.multiplicity-1)
    let T := S.intervalCompletion he
    let F := fun i => totalBetti (ZMod 2) T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing (ZMod 2)) (T.FormalTangentAlgebra (ZMod 2))) i
    v.choose 2+1 ≤ F 1 ∧ (3 ≤ v → 2*v.choose 3+v ≤ F 2) ∧
      (5 ≤ v → 3*v.choose 4+v.choose 2 ≤ F 3) ∧ 4*v.choose 5 ≤ F 4 :=
  S.interval_completed_TLOW (ZMod 2) he
end APLowerRowsAcceptance
