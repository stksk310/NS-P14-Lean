module

public import NSP14.Semigroup.ActualSidon
public import NSP14.Ordinary.QuadraticCutRank

@[expose] public section

open scoped Classical
open NSP14.Ordinary

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Prescribed numerical cut size, derived from actual Q₂. Existence of forms
of this size is the separate Green obligation, not part of this definition. -/
noncomputable def actualCutRank : ℕ := quadraticCutRank (S.degreeSet 2).card

theorem actualCutRank_two_le : 2 ≤ S.actualCutRank := quadraticCutRank_two_le _

theorem actualCutRank_le (he : 3 ≤ S.embeddingDimension) :
    S.actualCutRank ≤ S.embeddingDimension - 1 := by
  apply quadraticCutRank_le_of_bound (by omega)
  have hb := S.degree_two_card_le_quadratic
  simpa only [quadraticTriangular, Nat.sub_add_cancel (by omega : 1 ≤ S.embeddingDimension)] using hb

theorem actualCutRank_triangular (hr : 3 ≤ S.actualCutRank) :
    (S.actualCutRank + 1).choose 2 ≤ (S.degreeSet 2).card :=
  quadraticCutRank_triangular hr

/-- The maximal-cut implication is deliberately guarded by r≥3. -/
theorem actualCutRank_maximal (hr : 3 ≤ S.actualCutRank)
    (he : S.embeddingDimension = S.actualCutRank + 1) :
    (S.degreeSet 2).card = S.embeddingDimension.choose 2 := by
  have hl := S.actualCutRank_triangular hr
  rw [← he] at hl
  exact Nat.le_antisymm S.degree_two_card_le_quadratic hl

/-- The small-corner Sidon witness in the existing numerical closure is now
supplied by the actual semigroup; neither oddness nor primality of m is needed. -/
theorem actualNumericalBoundary :
    NumericalClosure.Boundary S.actualCutRank S.embeddingDimension S.deficit := by
  intro hr6 _ he
  have ha := S.actualCutRank_maximal (by omega) he
  have hm : S.multiplicity = S.embeddingDimension + S.deficit := by
    have := S.embeddingDimension_le_multiplicity
    unfold deficit
    omega
  have : NeZero S.multiplicity := ⟨Nat.ne_of_gt S.multiplicity_pos⟩
  rw [← hm]
  let D := S.actualAperyPairData ha
  exact ⟨D.residues, D.residues_sidon, D.residues_card⟩

variable (k : Type*) [Field k]

theorem actualCutRank_qDegree :
    S.actualCutRank = quadraticCutRank (Module.finrank k (S.qDegree k 2)) := by
  rw [S.qDegree_finrank]
  rfl

end NSP14.NumericalSemigroup
