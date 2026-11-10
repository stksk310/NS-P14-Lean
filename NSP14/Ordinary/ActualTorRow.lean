module
public import NSP14.Ordinary.RelativeTerminal
public import NSP14.Ordinary.CutBEuler
public import NSP14.Ordinary.CutHighTwo
public import NSP14.Ordinary.TowerRow
public import NSP14.Semigroup.ActualLayersField
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem cutAEuler_le_X2_B (j : ℕ) :
    C.cutAEuler j ≤ C.cutHighEuler 2 2 j+C.cutBEuler j := by
  have h := C.cutAEuler_le_high_B j
  rw [C.cutHeadHighEuler_two] at h
  exact h
end NSP14.NumericalSemigroup.LinearCutData
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

/-- Same actual x, fixed cut, tower and H. This is the full ordinary
Tor-to-resource comparison, including j=1 and j=r. -/
theorem actualTor_resource_row (j : ℕ) (hj : 1 ≤ j ∧ j ≤ W.source.actualCutRank) :
    letI := W.relativeG_finite
    (bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ) ≤
      TargetMargin.lower W.source.embeddingDimension W.source.actualCutRank j+
        (W.source.actualLayers k).row W.source.actualCutRank j W.source.deficit := by
  let := W.relativeG_finite
  have hx := W.relative_Euler_le (j-1)
  rw [Nat.sub_add_cancel hj.1] at hx
  have hB := W.cut.cutAEuler_le_X2_B j
  have hInt : bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j ≤
      W.cut.cutBEuler j+(W.cut.cutHighEuler 2 2 j+W.cut.cutTEuler (j-1)) := by omega
  have hQ : (bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ) ≤
      (W.cut.cutBEuler j : ℚ)+((W.cut.cutHighEuler 2 2 j+W.cut.cutTEuler (j-1) : ℤ) : ℚ) := by exact_mod_cast hInt
  rw [W.cut.cutBEuler_lower] at hQ
  have hrow := W.cut.cutTower_resource_row j hj
  rw [W.source.actualLayers_field_independent L k] at hrow
  linarith

/-- The existing Run14 numerical theorem is applied to the actual R-Tor
values, rather than to a hypothesized numerical c sequence. -/
theorem actualTor_target_row (j : ℕ) (hj : 1 ≤ j ∧ j ≤ W.source.actualCutRank) :
    letI := W.relativeG_finite
    (bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j : ℚ) ≤
      TargetMargin.target W.source.embeddingDimension W.source.deficit W.source.actualCutRank j :=
  (W.actualTor_resource_row j hj).trans (W.all_rows j hj)
end NSP14.Ordinary.ActualWitness
