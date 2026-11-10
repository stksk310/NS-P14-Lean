module
public import NSP14.Ordinary.NativeCutH0Z
public import NSP14.Ordinary.RelativeSomeKoszul
public import NSP14.Homological.RegularActionCoefficient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)
noncomputable abbrev nativeCoefficientCutComplex : ChainComplex (ModuleCat k) ℕ :=
  regularPartialCoefficientComplex k (S.TangentAlgebra k) C.nativeCutVariables
end NSP14.NumericalSemigroup.LinearCutData
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

theorem relativeNativeVariableOrder :
    W.relativeVariableOrder.map (fun x => W.relativeToG (MvPolynomial.X x))=W.cut.nativeCutVariables := by
  change (none::W.someVariables).map _=W.source.xElement L :: _
  rw [List.map_cons,W.relativeToG_X_none]
  congr 1
  rw [someVariables,List.map_map]
  apply List.map_congr_left
  intro i _
  exact W.relativeToG_X_some i

noncomputable def relativeRegularGIso :
    polynomialRegularModule L (Option (Fin W.source.actualCutRank)) (W.source.TangentAlgebra L) W.relativeToG ≅ W.relativeG := by
  let e : polynomialRegularModule L (Option (Fin W.source.actualCutRank)) (W.source.TangentAlgebra L) W.relativeToG ≃ₗ[W.RelativeRing] W.relativeG :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

/-- The native complex retains G and therefore all complement Z actions;
its coefficient complex is the actual relative R-variable complex. -/
noncomputable def relativeNativeKoszulIso : W.cut.nativeCoefficientCutComplex ≅
    (coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.relativeVariableOrder).obj W.relativeG := by
  have e := regularPartialPolynomialIso L (W.source.TangentAlgebra L)
    (Option (Fin W.source.actualCutRank)) W.relativeToG W.relativeVariableOrder
  rw [W.relativeNativeVariableOrder] at e
  exact e ≪≫ (coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.relativeVariableOrder).mapIso
    W.relativeRegularGIso

noncomputable def relativeNativeHomologyIso (i : ℕ) :
    W.cut.nativeCoefficientCutComplex.homology i ≅
      koszulHomologyK L (Option (Fin W.source.actualCutRank)) W.relativeG i :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso W.relativeNativeKoszulIso ≪≫
    (fullListHomologyKIso L (Option (Fin W.source.actualCutRank)) W.relativeVariableOrder
      W.mem_relativeVariableOrder W.relativeVariableOrder_nodup W.relativeG i).symm

theorem nativeRelativeHomology_finite (i : ℕ) : Module.Finite L (W.cut.nativeCoefficientCutComplex.homology i) := by
  let := W.relativeG_finite
  let := koszul_homology_finite L (Option (Fin W.source.actualCutRank)) W.relativeG i
  exact Module.Finite.equiv (W.relativeNativeHomologyIso i).symm.toLinearEquiv

theorem nativeRelativeBetti (i : ℕ) :
    letI := W.relativeG_finite
    Module.finrank L (W.cut.nativeCoefficientCutComplex.homology i)=
      totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG i := by
  let := W.relativeG_finite
  exact (W.relativeNativeHomologyIso i).toLinearEquiv.finrank_eq

theorem nativeRelativeEuler (j : ℕ) :
    letI := W.relativeG_finite
    complexEuler L W.cut.nativeCoefficientCutComplex j=
      bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j := by
  let := W.relativeG_finite
  rw [complexEuler_iso L W.relativeNativeKoszulIso]
  exact fullList_complexEuler L (Option (Fin W.source.actualCutRank)) W.relativeVariableOrder
    W.mem_relativeVariableOrder W.relativeVariableOrder_nodup W.relativeG j
end NSP14.Ordinary.ActualWitness
