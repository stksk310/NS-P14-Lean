module
public import NSP14.Ordinary.TowerGrading
public import NSP14.Ordinary.TowerEuler
public import NSP14.Homological.Harmonic
@[expose] public section
open CategoryTheory NSP14.Homological
open scoped BigOperators
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- Harmonic evaluation of the actual X_s/M_s truncations. The cut C is
identical in the action, the tower and the resource Hilbert function. -/
theorem cutHighEuler_harmonic (s n : ℕ) (hn : 1 ≤ n) (j : ℕ)
    (hj : 1 ≤ j ∧ j < S.actualCutRank) :
    (C.cutHighEuler s n j : ℚ) ≤ ((S.actualCutRank-1).choose j : ℚ)*
      ∑ t ∈ Finset.range (S.headTopDegree+1),((j : ℚ)/(t+j))*
        Module.finrank k (S.towerStageDegree k s (n+t)) := by
  let := C.cutHigh_finite s n
  let := C.cutHigh_coefficientFinite s n
  have hN (t : ℕ) (ht : S.headTopDegree < t) :
      CategoryTheory.Limits.IsZero ((C.cutHighGrading s n).piece ((n:ℤ)+t)) := by
    rw [← Nat.cast_add]
    exact C.cutHighGrading_vanish s n (n+t) (by omega)
  have h := harmonic_bound k S.actualCutRank (C.cutHigh s n) (C.cutHighGrading s n)
    (n:ℤ) S.headTopDegree (C.cutHighGrading_generated s n hn) hN j hj
  change (C.cutHighEuler s n j : ℚ) ≤ _ at h
  have hf (t : ℕ) : Module.finrank k ((C.cutHighGrading s n).piece ((n:ℤ)+t))=
      Module.finrank k (S.towerStageDegree k s (n+t)) := by
    rw [← Nat.cast_add]
    exact C.cutHighGrading_finrank s n (n+t) (Nat.le_add_right n t)
  simpa only [hf] using h
end NSP14.NumericalSemigroup.LinearCutData
