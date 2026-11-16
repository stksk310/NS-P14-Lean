module
public import NSP14.Semigroup.AlgebraXSequences
public import NSP14.Ordinary.CutFinite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutToG : S.CutPolynomialRing k →ₐ[k] S.TangentAlgebra k :=
  (S.polynomialToG k).comp C.toPolynomialRing

noncomputable def algebraRestriction : ModuleCat (S.TangentAlgebra k) ⥤ ModuleCat (S.CutPolynomialRing k) :=
  ModuleCat.restrictScalars C.cutToG.toRingHom

noncomputable def algebraRestrictionGIso : C.algebraRestriction.obj (S.algebraG k) ≅ C.cutG := by
  let e : C.algebraRestriction.obj (S.algebraG k) ≃ₗ[S.CutPolynomialRing k] C.cutG :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

noncomputable def algebraRestrictionTIso : C.algebraRestriction.obj (S.algebraT k) ≅ C.cutT := by
  let e : C.algebraRestriction.obj (S.algebraT k) ≃ₗ[S.CutPolynomialRing k] C.cutT :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso

noncomputable def algebraRestrictionAIso : C.algebraRestriction.obj (S.algebraA k) ≅ C.cutA := by
  let e : C.algebraRestriction.obj (S.algebraA k) ≃ₗ[S.CutPolynomialRing k] C.cutA :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso
end NSP14.NumericalSemigroup.LinearCutData
