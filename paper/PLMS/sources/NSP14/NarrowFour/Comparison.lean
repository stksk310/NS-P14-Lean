module
public import NSP14.NarrowFour.WidthFourComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.NarrowFour

/-- Both completed cones retain their own actual minimal presentations. -/
theorem completed_carrier_betti (S T : NumericalSemigroup) (h : S.carrier=T.carrier)
    (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i=
      totalBetti k T.AtomExponent (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i := by
  rw [←S.completed_totalBetti k,←T.completed_totalBetti k]
  exact S.carrier_totalBetti T h k i

/-- The literal completion is also independent of a chosen cofinite witness. -/
theorem interval_carrier_betti (S T : NumericalSemigroup) (h : S.carrier=T.carrier)
    (k : Type) [Field k] (heS : 2 ≤ S.embeddingDimension) (heT : 2 ≤ T.embeddingDimension) (i : ℕ) :
    totalBetti k (S.intervalCompletion heS).AtomExponent
      (ModuleCat.of ((S.intervalCompletion heS).FullPolynomialRing k)
        ((S.intervalCompletion heS).FormalTangentAlgebra k)) i=
      totalBetti k (T.intervalCompletion heT).AtomExponent
        (ModuleCat.of ((T.intervalCompletion heT).FullPolynomialRing k)
          ((T.intervalCompletion heT).FormalTangentAlgebra k)) i := by
  cases S;cases T;cases h;rfl

/-- The entire original four-generator narrow branch: all physical widths, all fields,
all rows, and no extra resource or comparison premise. -/
theorem narrow_four_comparison (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :
    let he2 : 2 ≤ S.embeddingDimension := by omega
    ∀ i : ℕ,totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion he2).AtomExponent
        (ModuleCat.of ((S.intervalCompletion he2).FullPolynomialRing k)
          ((S.intervalCompletion he2).FormalTangentAlgebra k)) i := by
  dsimp only
  intro i
  by_cases hi0 : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  by_cases hi2 : 2 ≤ i
  · exact narrow_four_higher S k he hw i hi2
  have hi1 : i=1 := by omega
  subst i
  let D := S.endpointData (by omega) hw
  have hq : D.q=2 := by
    have h := S.endpointData_embedding (by omega) hw
    change D.q+2=S.embeddingDimension at h
    omega
  have hu : 3 ≤ D.u := by have := D.q_add_one_le_u;omega
  by_cases hlarge : D.u=5 ∨ 9 ≤ D.u
  · exact narrow_four_first_large k S he hw hlarge
  by_cases hspecial : D.u=4 ∧ D.d=1 ∧ D.a={1,3}
  · have hm := S.endpointData_narrow (by omega) hw
    change D.d*D.u+2 ≤ D.m at hm
    have hm6 : 6 ≤ D.m := by rw [hspecial.1,hspecial.2.1] at hm;omega
    have hDS : D.source.carrier=S.carrier := S.endpointData_carrier (by omega) hw
    have heD : 2 ≤ D.source.embeddingDimension := by rw [D.embeddingDimension,hq];omega
    rw [completed_carrier_betti S D.source hDS.symm k 1,
      interval_carrier_betti S D.source hDS.symm k (by omega) heD 1]
    exact WidthFour.width_four_comparison D k hq hm6 hspecial.2.1 hspecial.1 hspecial.2.2 1
  · have hsmall : D.u=3 ∨ D.u=5 ∨ D.u=6 ∨ D.u=7 ∨ D.u=8 ∨
        (D.u=4 ∧ (D.d≠1 ∨ D.a≠{1,3})) := by
      by_cases h4 : D.u=4
      · have ho : D.d≠1 ∨ D.a≠{1,3} := by
          by_cases hd : D.d=1
          · exact Or.inr (fun ha => hspecial ⟨h4,hd,ha⟩)
          · exact Or.inl hd
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4,ho⟩))))
      · have hc : D.u=3 ∨ D.u=6 ∨ D.u=7 ∨ D.u=8 := by omega
        rcases hc with h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact narrow_four_small S k he hw hsmall 1
end NSP14.NarrowFour
