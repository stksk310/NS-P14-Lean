module
public import NSP14.Target.IntervalAPBetti
@[expose] public section
namespace NSP14.Target

/-- The four TLOW rows used in the width branches, including the odd
endpoints where consecutive binomial coefficients are equal. -/
theorem apLowerProfile_TLOW_one (v : ℕ) (hv : 1 ≤ v) :
    v.choose 2+1 ≤ apLowerProfile v 1 := by
  simp [apLowerProfile,min_eq_left hv]

theorem apLowerProfile_TLOW_two (v : ℕ) (hv : 3 ≤ v) :
    2*v.choose 3+v ≤ apLowerProfile v 2 := by
  have hc : v ≤ v.choose 2 := by
    by_cases h : v=3
    · subst v;decide
    · have h4 : 4 ≤ v := by omega
      simpa using (Nat.choose_le_succ_of_lt_half_left (r:=1) (n:=v) (by omega))
  simp [apLowerProfile,min_eq_left hc]

theorem apLowerProfile_TLOW_three (v : ℕ) (hv : 5 ≤ v) :
    3*v.choose 4+v.choose 2 ≤ apLowerProfile v 3 := by
  have hc : v.choose 2 ≤ v.choose 3 := by
    by_cases h : v=5
    · subst v;decide
    · have h6 : 6 ≤ v := by omega
      exact Nat.choose_le_succ_of_lt_half_left (r:=2) (n:=v) (by omega)
  change 3*v.choose 4+v.choose 2 ≤ 3*v.choose 4+min (v.choose 2) (v.choose 3)
  rw [min_eq_left hc]

theorem apLowerProfile_TLOW_four (v : ℕ) : 4*v.choose 5 ≤ apLowerProfile v 4 := by
  exact Nat.le_add_right _ _
end NSP14.Target
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

theorem positiveBettiProfile_TLOW_one : D.v.choose 2+1 ≤ D.positiveBettiProfile 1 :=
  (NSP14.Target.apLowerProfile_TLOW_one D.v D.v_pos).trans (D.positiveBettiProfile_lower 1)

theorem positiveBettiProfile_TLOW_two (hv : 3 ≤ D.v) :
    2*D.v.choose 3+D.v ≤ D.positiveBettiProfile 2 :=
  (NSP14.Target.apLowerProfile_TLOW_two D.v hv).trans (D.positiveBettiProfile_lower 2)

theorem positiveBettiProfile_TLOW_three (hv : 5 ≤ D.v) :
    3*D.v.choose 4+D.v.choose 2 ≤ D.positiveBettiProfile 3 :=
  (NSP14.Target.apLowerProfile_TLOW_three D.v hv).trans (D.positiveBettiProfile_lower 3)

theorem positiveBettiProfile_TLOW_four : 4*D.v.choose 5 ≤ D.positiveBettiProfile 4 :=
  (NSP14.Target.apLowerProfile_TLOW_four D.v).trans (D.positiveBettiProfile_lower 4)
end NSP14.ArithmeticSequence.Data
namespace NSP14.NumericalSemigroup
open NSP14.Homological
variable (S : NumericalSemigroup) (k : Type) [Field k]

/-- The explicit TLOW rows on the literal completed interval target,
with the target's own actual minimal variables in every row. -/
theorem interval_completed_TLOW (he : 2 ≤ S.embeddingDimension) :
    let v := min S.width (S.multiplicity-1)
    let T := S.intervalCompletion he
    let F := fun i => totalBetti k T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i
    v.choose 2+1 ≤ F 1 ∧ (3 ≤ v → 2*v.choose 3+v ≤ F 2) ∧
      (5 ≤ v → 3*v.choose 4+v.choose 2 ≤ F 3) ∧ 4*v.choose 5 ≤ F 4 := by
  dsimp only
  simp only [S.interval_completed_betti_profile k he 1 (by decide),
    S.interval_completed_betti_profile k he 2 (by decide),
    S.interval_completed_betti_profile k he 3 (by decide),
    S.interval_completed_betti_profile k he 4 (by decide)]
  exact ⟨(S.intervalAP he).positiveBettiProfile_TLOW_one,
    (S.intervalAP he).positiveBettiProfile_TLOW_two,
    (S.intervalAP he).positiveBettiProfile_TLOW_three,
    (S.intervalAP he).positiveBettiProfile_TLOW_four⟩
end NSP14.NumericalSemigroup
