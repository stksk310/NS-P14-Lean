module
public import NSP14.Ordinary.CutXSequences
public import NSP14.Ordinary.JumpEuler
public import NSP14.Homological.TwoStepCone
public import NSP14.Homological.CoefficientKoszulFunctor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- The actual x mapping cone on the P Koszul complex of G. Its chain
groups are allowed to be infinite dimensional. -/
noncomputable def cutXKoszulCone : ChainComplex (ModuleCat k) ℕ :=
  homotopyCofiber ((coefficientKoszulFunctor k (Fin S.actualCutRank)).map C.cutX)

noncomputable def cutAEuler (j : ℕ) : ℤ := by
  let := C.cutA_finite
  exact bettiEuler k (Fin S.actualCutRank) C.cutA j

/-- The first x comparison is proved on the actual complex, via two actual
exact sequences. It retains the possible higher connecting correction.
Identification with ordinary Tor over R is a separate subsequent transport. -/
theorem cutXKoszulCone_Euler_le (j : ℕ) :
    complexEuler k C.cutXKoszulCone (j+1) ≤ C.cutAEuler (j+1)+C.cutTEuler j := by
  let F := coefficientKoszulFunctor k (Fin S.actualCutRank)
  let := C.cutT_finite
  let := C.cutA_finite
  let hfiniteT : ∀ i,Module.Finite k ((F.obj C.cutT).homology i) := fun i => by
    exact coefficientKoszulFunctor_homologyFinite k (Fin S.actualCutRank) C.cutT i
  let hfiniteA : ∀ i,Module.Finite k ((F.obj C.cutA).homology i) := fun i => by
    exact coefficientKoszulFunctor_homologyFinite k (Fin S.actualCutRank) C.cutA i
  have hfg : F.map C.cutTerminalInclusion ≫ F.map C.cutXRangeProjection=0 := by
    rw [← F.map_comp,C.cutTerminalInclusion_comp,F.map_zero]
  have hab : F.map C.cutXRangeInclusion ≫ F.map C.cutHeadProjection=0 := by
    rw [← F.map_comp,C.cutXRangeInclusion_comp,F.map_zero]
  have h₁ := coefficientKoszulFunctor_shortExact k (Fin S.actualCutRank)
    C.cutXKernelSequence C.cutXKernelSequence_shortExact
  have h₂ := coefficientKoszulFunctor_shortExact k (Fin S.actualCutRank)
    C.cutXQuotientSequence C.cutXQuotientSequence_shortExact
  unfold cutXKernelSequence at h₁
  unfold cutXQuotientSequence at h₂
  dsimp only [ShortComplex.map] at h₁ h₂
  have h := @factorCone_Euler_comparison k _
    (F.obj C.cutT) (F.obj C.cutG) (F.obj C.cutXImage) (F.obj C.cutA)
    (F.map C.cutTerminalInclusion) (F.map C.cutXRangeProjection)
    (F.map C.cutXRangeInclusion) (F.map C.cutHeadProjection) hfg hab h₁ h₂ hfiniteT hfiniteA j
  rw [← F.map_comp,C.cutXRange_factor] at h
  simpa only [F,complexEuler_coefficientKoszul,cutXKoszulCone,cutAEuler,cutTEuler] using h
end NSP14.NumericalSemigroup.LinearCutData
