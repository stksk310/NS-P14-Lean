module
public import NSP14.Semigroup.HeadResource
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

/-- All resource inequalities come from this actual semigroup's single H.
For a finite field only the cut construction is made over the fixed infinite
same-characteristic extension; H itself is proved field-independent. -/
noncomputable def actualNumericalDataWithCut (he : 3 ≤ S.embeddingDimension)
    (C : S.LinearCutData (NSP14.Homological.InfiniteScalarField k)) :
    NSP14.Ordinary.NumericalClosure.Data S.actualCutRank S.embeddingDimension S.deficit where
  layers := S.actualLayers k
  rank_lo := S.actualCutRank_two_le
  embed := by have := S.actualCutRank_le he; omega
  budget := S.actualLayers_budget k
  head_linear := by
    have h := S.towerResource_head_linear (NSP14.Homological.InfiniteScalarField k) C
    rw [← S.towerResource_field_independent k (NSP14.Homological.InfiniteScalarField k) 1] at h
    change (S.towerResource k 1 : ℚ) ≤ _
    exact_mod_cast h
  triangular_bound hr := by
    have h := (S.actualCutRank_triangular hr).trans S.degree_two_le_deficit
    have hc : NSP14.Ordinary.SmallScalar.triangular S.actualCutRank =
        (((S.actualCutRank+1).choose 2 : ℕ) : ℚ) := by
      rw [← NSP14.Ordinary.LargeSeed.triangularNat_cast]
      unfold NSP14.Ordinary.LargeSeed.triangularNat
      congr 1
      simp only [Nat.choose_two_right,Nat.add_sub_cancel,Nat.mul_comm]
    rw [hc]
    exact_mod_cast h
  head_cap hr := by
    have h := S.towerResource_head_cap k
    have ha := S.actualCutRank_triangular hr
    have hm := S.multiplicity_eq_embedding_add_deficit
    have hp := S.multiplicity_pos
    have heq := NSP14.Ordinary.LargeSeed.triangularNat_cast S.actualCutRank
    have htri : NSP14.Ordinary.SmallScalar.triangular S.actualCutRank =
        (((S.actualCutRank+1).choose 2 : ℕ) : ℚ) := by
      rw [← heq]
      unfold NSP14.Ordinary.LargeSeed.triangularNat
      congr 1
      simp only [Nat.choose_two_right,Nat.add_sub_cancel,Nat.mul_comm]
    change (S.towerResource k 1 : ℚ) ≤ _
    rw [htri]
    have hcast : (S.towerResource k 1 : ℚ)+((S.actualCutRank+1).choose 2 : ℕ) ≤
        (S.embeddingDimension : ℚ)+S.deficit-1 := by
      have hn : S.towerResource k 1+(S.actualCutRank+1).choose 2+1 ≤ S.embeddingDimension+S.deficit := by omega
      have hq : (S.towerResource k 1 : ℚ)+((S.actualCutRank+1).choose 2 : ℕ)+1 ≤
          (S.embeddingDimension : ℚ)+S.deficit := by exact_mod_cast hn
      linarith
    linarith
  tail_cap j := by
    have h := S.towerResource_le_multiplicity k (j+2)
    have hm := S.multiplicity_eq_embedding_add_deficit
    have hp := S.multiplicity_pos
    change (S.towerResource k (j+2) : ℚ) ≤ _
    have hn : S.towerResource k (j+2)+1 ≤ S.embeddingDimension+S.deficit := by omega
    have hc : (S.towerResource k (j+2) : ℚ)+1 ≤ (S.embeddingDimension : ℚ)+S.deficit := by exact_mod_cast hn
    linarith

noncomputable def actualNumericalData (he : 3 ≤ S.embeddingDimension) :
    NSP14.Ordinary.NumericalClosure.Data S.actualCutRank S.embeddingDimension S.deficit :=
  S.actualNumericalDataWithCut k he (S.infiniteFieldCut k he)

/-- Existing numerical row closure, now supplied by actual resources and
actual Sidon evidence. The Tor-to-row and target Betti identification is Run15. -/
theorem actual_all_rows (he : 3 ≤ S.embeddingDimension) :
    ∀ i, 1 ≤ i ∧ i ≤ S.actualCutRank →
      NSP14.Ordinary.TargetMargin.lower S.embeddingDimension S.actualCutRank i +
        (S.actualLayers k).row S.actualCutRank i S.deficit ≤
      NSP14.Ordinary.TargetMargin.target S.embeddingDimension S.deficit S.actualCutRank i :=
  (S.actualNumericalData k he).all_rows S.actualNumericalBoundary
end NSP14.NumericalSemigroup
