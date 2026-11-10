module
public import NSP14.Ordinary.RelativeConeBetti
public import NSP14.Homological.FiniteKoszulEulerAbove
public import NSP14.Homological.CoefficientFactorCone
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

theorem someKoszulT_Euler (j : ℕ) :
    complexEuler L (W.someKoszulFunctor.obj (W.source.algebraT L)) j=W.cut.cutTEuler j := by
  let := W.cut.cutT_finite
  rw [complexEuler_iso L W.someKoszulTIso,coefficientKoszulListFunctor_full]
  exact complexEuler_coefficientKoszul L (Fin W.source.actualCutRank) W.cut.cutT j

theorem someKoszulA_Euler (j : ℕ) :
    complexEuler L (W.someKoszulFunctor.obj (W.source.algebraA L)) j=W.cut.cutAEuler j := by
  let := W.cut.cutA_finite
  rw [complexEuler_iso L W.someKoszulAIso,coefficientKoszulListFunctor_full]
  exact complexEuler_coefficientKoszul L (Fin W.source.actualCutRank) W.cut.cutA j

/-- The actual first x comparison over R, which has r+1 variables.
Only the endpoints of the two exact sequences have finite P homology. -/
theorem relative_Euler_le (j : ℕ) :
    letI := W.relativeG_finite
    bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG (j+1) ≤
      W.cut.cutAEuler (j+1)+W.cut.cutTEuler j := by
  let hfiniteT : ∀ i,Module.Finite L (((coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.someVariables).obj (W.algebraRestriction.obj (W.source.algebraT L))).homology i) := fun i => by
    have h := W.someKoszulT_homologyFinite i
    rw [W.someKoszulFunctor_obj] at h
    exact h
  let hfiniteA : ∀ i,Module.Finite L (((coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.someVariables).obj (W.algebraRestriction.obj (W.source.algebraA L))).homology i) := fun i => by
    have h := W.someKoszulA_homologyFinite i
    rw [W.someKoszulFunctor_obj] at h
    exact h
  have hfg : W.algebraRestriction.map (W.source.algebraTerminalInclusion L) ≫ W.algebraRestriction.map (W.source.algebraXProjection L)=0 := by
    rw [← W.algebraRestriction.map_comp,W.source.algebraTerminal_comp,W.algebraRestriction.map_zero]
  have hab : W.algebraRestriction.map (W.source.algebraImageInclusion L) ≫ W.algebraRestriction.map (W.source.algebraHeadProjection L)=0 := by
    rw [← W.algebraRestriction.map_comp,W.source.algebraImage_comp,W.algebraRestriction.map_zero]
  have h₁ : ((W.source.algebraKernelSequence L).map W.algebraRestriction).ShortExact := by
    exact (W.source.algebraKernelSequence_shortExact L).map_of_exact
      (ModuleCat.restrictScalars W.relativeToG.toRingHom)
  have h₂ : ((W.source.algebraHeadSequence L).map W.algebraRestriction).ShortExact := by
    exact (W.source.algebraHeadSequence_shortExact L).map_of_exact
      (ModuleCat.restrictScalars W.relativeToG.toRingHom)
  unfold NumericalSemigroup.algebraKernelSequence at h₁
  unfold NumericalSemigroup.algebraHeadSequence at h₂
  dsimp only [ShortComplex.map] at h₁ h₂
  have h := @coefficientFactorCone_Euler_comparison L (Option (Fin W.source.actualCutRank)) _ W.someVariables
    (W.algebraRestriction.obj (W.source.algebraT L)) (W.algebraRestriction.obj (W.source.algebraG L))
    (W.algebraRestriction.obj (W.source.algebraI L)) (W.algebraRestriction.obj (W.source.algebraA L))
    (W.algebraRestriction.map (W.source.algebraTerminalInclusion L)) (W.algebraRestriction.map (W.source.algebraXProjection L))
    (W.algebraRestriction.map (W.source.algebraImageInclusion L)) (W.algebraRestriction.map (W.source.algebraHeadProjection L))
    hfg hab h₁ h₂ hfiniteT hfiniteA j
  rw [← W.algebraRestriction.map_comp] at h
  have hA := W.someKoszulA_Euler (j+1)
  have hT := W.someKoszulT_Euler j
  rw [W.someKoszulFunctor_obj] at hA hT
  change complexEuler L W.relativeSomeCone (j+1) ≤ _ at h
  rw [W.relativeSomeCone_Euler,hA,hT] at h
  exact h

end NSP14.Ordinary.ActualWitness
