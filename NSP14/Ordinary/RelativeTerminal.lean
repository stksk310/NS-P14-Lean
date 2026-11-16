module
public import NSP14.Ordinary.RelativeXComparison
public import NSP14.Homological.FactorConeTerminal
public import NSP14.Homological.CoefficientKoszulSupport
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem cutTEuler_eq_zero_of_ge (j : ℕ) (hj : S.actualCutRank ≤ j) : C.cutTEuler j=0 := by
  let := C.cutT_finite
  let := C.cutT_coefficientFinite
  exact finite_koszul_bettiEuler_eq_zero_of_ge k (Fin S.actualCutRank) C.cutT
    (by simpa only [Fintype.card_fin] using (show 1 ≤ S.actualCutRank by have := S.actualCutRank_two_le;omega)) j
    (by simpa only [Fintype.card_fin] using hj)

theorem cutAEuler_eq_zero_of_ge (j : ℕ) (hj : S.actualCutRank ≤ j) : C.cutAEuler j=0 := by
  let := C.cutA_finite
  let := C.cutA_coefficientFinite
  exact finite_koszul_bettiEuler_eq_zero_of_ge k (Fin S.actualCutRank) C.cutA
    (by simpa only [Fintype.card_fin] using (show 1 ≤ S.actualCutRank by have := S.actualCutRank_two_le;omega)) j
    (by simpa only [Fintype.card_fin] using hj)
end NSP14.NumericalSemigroup.LinearCutData
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

theorem someKoszulA_homology_isZero_of_gt (i : ℕ) (hi : W.source.actualCutRank < i) :
    IsZero ((W.someKoszulFunctor.obj (W.source.algebraA L)).homology i) := by
  apply complex_homology_isZero_of_iso L W.someKoszulAIso i
  exact coefficientKoszulList_homology_isZero_of_gt L (Fin W.source.actualCutRank)
    (variableList L (Fin W.source.actualCutRank)) W.cut.cutA i
    (by simpa only [variableList_length,Fintype.card_fin] using hi)

/-- The source is finite over R, not finite over P or over L. Its terminal
Euler row is r+1 because R has r+1 variables. The connecting correction
vanishes here by the genuine support of the endpoint complex. -/
theorem relative_Euler_terminal :
    letI := W.relativeG_finite
    bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG (W.source.actualCutRank+1)=0 := by
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
  have hK : complexEuler L ((coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.someVariables).obj (W.algebraRestriction.obj (W.source.algebraT L))) W.source.actualCutRank=0 := by
    have h := W.someKoszulT_Euler W.source.actualCutRank
    rw [W.someKoszulFunctor_obj] at h
    rw [h,W.cut.cutTEuler_eq_zero_of_ge _ le_rfl]
  have hA : complexEuler L ((coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.someVariables).obj (W.algebraRestriction.obj (W.source.algebraA L))) (W.source.actualCutRank+1)=0 := by
    have h := W.someKoszulA_Euler (W.source.actualCutRank+1)
    rw [W.someKoszulFunctor_obj] at h
    rw [h,W.cut.cutAEuler_eq_zero_of_ge _ (by omega)]
  have hz := W.someKoszulA_homology_isZero_of_gt (W.source.actualCutRank+2) (by omega)
  rw [W.someKoszulFunctor_obj] at hz
  have h := @coefficientFactorCone_Euler_zero L (Option (Fin W.source.actualCutRank)) _ W.someVariables
    (W.algebraRestriction.obj (W.source.algebraT L)) (W.algebraRestriction.obj (W.source.algebraG L))
    (W.algebraRestriction.obj (W.source.algebraI L)) (W.algebraRestriction.obj (W.source.algebraA L))
    (W.algebraRestriction.map (W.source.algebraTerminalInclusion L)) (W.algebraRestriction.map (W.source.algebraXProjection L))
    (W.algebraRestriction.map (W.source.algebraImageInclusion L)) (W.algebraRestriction.map (W.source.algebraHeadProjection L))
    hfg hab h₁ h₂ hfiniteT hfiniteA W.source.actualCutRank hK hA hz
  rw [← W.algebraRestriction.map_comp] at h
  change complexEuler L W.relativeSomeCone (W.source.actualCutRank+1)=0 at h
  rw [W.relativeSomeCone_Euler] at h
  exact h

end NSP14.Ordinary.ActualWitness
