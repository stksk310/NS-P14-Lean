module
public import NSP14.Ordinary.RelativeAlgebraRestriction
public import NSP14.Ordinary.CutXComparison
public import NSP14.Homological.CoefficientKoszulListFunctor
public import NSP14.Homological.FullListBetti
public import NSP14.Homological.KoszulLinearity
@[expose] public section
set_option backward.isDefEq.respectTransparency true
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

noncomputable def someVariables : List (Option (Fin W.source.actualCutRank)) :=
  (variableList L (Fin W.source.actualCutRank)).map some

noncomputable abbrev relativeVariableOrder : List (Option (Fin W.source.actualCutRank)) := none :: W.someVariables

theorem relativeVariableOrder_nodup : W.relativeVariableOrder.Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp [someVariables]
  · exact (variableList_nodup L (Fin W.source.actualCutRank)).map (Option.some_injective _)

theorem mem_relativeVariableOrder (x : Option (Fin W.source.actualCutRank)) : x ∈ W.relativeVariableOrder := by
  cases x with
  | none => exact List.mem_cons_self
  | some i => exact List.mem_cons_of_mem none (List.mem_map.mpr ⟨i,mem_variableList L _ i,rfl⟩)

noncomputable abbrev someKoszulFunctor : ModuleCat (W.source.TangentAlgebra L) ⥤ ChainComplex (ModuleCat L) ℕ :=
  W.algebraRestriction ⋙ coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.someVariables

noncomputable instance someKoszulFunctor_additive : W.someKoszulFunctor.Additive := by
  unfold someKoszulFunctor algebraRestriction
  infer_instance

theorem someKoszulFunctor_obj (M : ModuleCat (W.source.TangentAlgebra L)) :
    W.someKoszulFunctor.obj M=
      (coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank))
        W.someVariables).obj
        (W.algebraRestriction.obj M) := by
  unfold someKoszulFunctor
  dsimp only [Functor.comp_obj]

noncomputable def someKoszulTIso : W.someKoszulFunctor.obj (W.source.algebraT L) ≅
    (coefficientKoszulListFunctor L (Fin W.source.actualCutRank) (variableList L (Fin W.source.actualCutRank))).obj W.cut.cutT := by
  let eP : (ModuleCat.restrictScalars W.cutToRelative.toRingHom).obj
      (W.algebraRestriction.obj (W.source.algebraT L)) ≅ W.cut.cutT :=
    (W.cutRestrictionIso.app (W.source.algebraT L)).symm ≪≫ W.cut.algebraRestrictionTIso
  rw [someKoszulFunctor_obj,someVariables]
  exact coefficientRestrictionKoszulModuleIso L (Option (Fin W.source.actualCutRank)) (Fin W.source.actualCutRank)
    W.cutToRelative some W.cutToRelative_X (variableList L (Fin W.source.actualCutRank))
    (W.algebraRestriction.obj (W.source.algebraT L)) W.cut.cutT eP

noncomputable def someKoszulAIso : W.someKoszulFunctor.obj (W.source.algebraA L) ≅
    (coefficientKoszulListFunctor L (Fin W.source.actualCutRank) (variableList L (Fin W.source.actualCutRank))).obj W.cut.cutA := by
  let eP : (ModuleCat.restrictScalars W.cutToRelative.toRingHom).obj
      (W.algebraRestriction.obj (W.source.algebraA L)) ≅ W.cut.cutA :=
    (W.cutRestrictionIso.app (W.source.algebraA L)).symm ≪≫ W.cut.algebraRestrictionAIso
  rw [someKoszulFunctor_obj,someVariables]
  exact coefficientRestrictionKoszulModuleIso L (Option (Fin W.source.actualCutRank)) (Fin W.source.actualCutRank)
    W.cutToRelative some W.cutToRelative_X (variableList L (Fin W.source.actualCutRank))
    (W.algebraRestriction.obj (W.source.algebraA L)) W.cut.cutA eP

theorem someKoszulT_homologyFinite (i : ℕ) :
    Module.Finite L ((W.someKoszulFunctor.obj (W.source.algebraT L)).homology i) := by
  let := W.cut.cutT_finite
  let := coefficientKoszulListFunctor_full_homologyFinite L (Fin W.source.actualCutRank) W.cut.cutT i
  exact complex_homologyFinite_of_iso L W.someKoszulTIso i

theorem someKoszulA_homologyFinite (i : ℕ) :
    Module.Finite L ((W.someKoszulFunctor.obj (W.source.algebraA L)).homology i) := by
  let := W.cut.cutA_finite
  let := coefficientKoszulListFunctor_full_homologyFinite L (Fin W.source.actualCutRank) W.cut.cutA i
  exact complex_homologyFinite_of_iso L W.someKoszulAIso i

theorem someKoszulFunctor_shortExact (S : ShortComplex (ModuleCat (W.source.TangentAlgebra L))) (hS : S.ShortExact) :
    (S.map W.someKoszulFunctor).ShortExact := by
  unfold someKoszulFunctor
  rw [ShortComplex.map_comp]
  have hR : (S.map W.algebraRestriction).ShortExact := by
    unfold algebraRestriction
    exact hS.map_of_exact (ModuleCat.restrictScalars W.relativeToG.toRingHom)
  exact coefficientKoszulListFunctor_shortExact L (Option (Fin W.source.actualCutRank)) W.someVariables _ hR

theorem relative_algebraX_scalar :
    W.algebraRestriction.map (W.source.algebraXProjection L ≫ W.source.algebraImageInclusion L)=
      (MvPolynomial.X none : W.RelativeRing) • 𝟙 (W.algebraRestriction.obj (W.source.algebraG L)) := by
  ext a
  change (show W.source.TangentAlgebra L from a)*W.source.xElement L=
    W.relativeToG (MvPolynomial.X none)*(show W.source.TangentAlgebra L from a)
  rw [relativeToG_X_none,mul_comm]
end NSP14.Ordinary.ActualWitness
