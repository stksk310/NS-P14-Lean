module
public import audit.run14.RemainingGoals
@[expose] public section
open scoped Classical BigOperators
open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary NSP14.Homological
namespace Run14Closed

 theorem green (S : NumericalSemigroup) (k : Type) [Field k] : Run14Remaining.GreenDegreeTwoGoal S k := by
  intro hk
  have : Infinite k := hk
  obtain ⟨c,hc,hs⟩ := S.actual_green_flag k
  refine ⟨fun i => S.headLinearCoordinates k (c i),hc.map' (S.headLinearCoordinates k).toLinearMap (S.headLinearCoordinates k).ker,?_⟩
  intro s hsp
  have h := hs s hsp
  have hl : ∀ i, S.polynomialToA k (Run14Remaining.linearPolynomial S k
      (S.headLinearCoordinates k (c i))) = (c i).val := by
    intro i
    change S.polynomialToA k (S.linearFormPolynomial k (S.headLinearCoordinates k (c i))) = _
    rw [S.polynomialToA_linearForm,S.linearHeadMap_coordinates]
  have hi : Run14Remaining.partialCutIdeal S k _ (fun i => S.headLinearCoordinates k (c i)) s =
      S.linearCutIdeal k c s := by
    apply congrArg (Ideal.span)
    ext a
    constructor
    · rintro ⟨i,his,he⟩
      exact ⟨i,his,he.trans (hl i)⟩
    · rintro ⟨i,his,he⟩
      exact ⟨i,his,he.trans (hl i).symm⟩
  have hd : Module.finrank k (Run14Remaining.cutDegree S k _ (fun i => S.headLinearCoordinates k (c i)) s 2) =
      Module.finrank k (S.linearCutDegree k c s 2) :=
    congrArg (fun I : Ideal (S.HeadAlgebra k) => Module.finrank k
      ((S.headDegree k 2).map (Ideal.Quotient.mkₐ k I).toLinearMap)) hi
  exact hd ▸ h

 theorem one_cut (S : NumericalSemigroup) (k : Type) [Field k] : Run14Remaining.OneCutGoal S k := by
  intro he
  let C := S.infiniteFieldCut k he
  refine ⟨fun i => S.headLinearCoordinates (InfiniteScalarField k) (C.forms i),
    C.independent.map' (S.headLinearCoordinates (InfiniteScalarField k)).toLinearMap
      (S.headLinearCoordinates (InfiniteScalarField k)).ker,?_⟩
  intro n hn a ha
  have h := LinearCutData.high_mem S (InfiniteScalarField k) C n hn a ha
  have hl : ∀ i, S.polynomialToA (InfiniteScalarField k) (Run14Remaining.linearPolynomial S (InfiniteScalarField k)
      (S.headLinearCoordinates (InfiniteScalarField k) (C.forms i))) = (C.forms i).val := by
    intro i
    change S.polynomialToA (InfiniteScalarField k) (C.polynomialForm i) = _
    exact C.polynomialForm_image i
  simpa only [Run14Remaining.partialCutIdeal,hl,linearCutIdeal] using h

 theorem volume (S : NumericalSemigroup) : Run14Remaining.SharpOffsetVolumeGoal S := S.offset_volume_bound

 theorem resources (S : NumericalSemigroup) (k : Type) [Field k] :
    Run14Remaining.ResourceBoundsGoal S k := by
  refine ⟨S.actualLayers_budget k,S.towerResource_le_multiplicity k,?_,?_⟩
  · by_cases he : 3 ≤ S.embeddingDimension
    · exact (S.actualNumericalData k he).head_linear
    · by_cases hd : S.deficit=0
      · rw [S.towerResource_eq_zero_of_deficit_zero k hd 1,hd]
        norm_num
      · have hi := S.towerResource_head_identity k
        have hl := S.terminalLinearCount_le
        have hr := Nat.mul_le_mul_right S.deficit S.actualCutRank_two_le
        have hn : S.towerResource k 1 ≤ S.actualCutRank*S.deficit := by omega
        exact_mod_cast hn
  · intro hr
    have h := S.towerResource_head_cap k
    have ha := S.actualCutRank_triangular hr
    have hm := S.multiplicity_pos
    have hn : S.towerResource k 1+(S.actualCutRank+1).choose 2+1 ≤ S.multiplicity := by omega
    have hc : (S.towerResource k 1 : ℚ)+((S.actualCutRank+1).choose 2 : ℕ)+1 ≤ S.multiplicity := by exact_mod_cast hn
    linarith

 theorem numerical_data (S : NumericalSemigroup) (k : Type) [Field k] :
    Run14Remaining.ActualNumericalDataGoal S k := fun he => ⟨S.actualNumericalData k he,rfl⟩
end Run14Closed
