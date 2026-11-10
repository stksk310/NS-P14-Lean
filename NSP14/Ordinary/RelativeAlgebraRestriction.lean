module
public import NSP14.Ordinary.CutAlgebraRestriction
public import NSP14.Ordinary.RelativeFinite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)

noncomputable def cutToRelative : W.source.CutPolynomialRing (ScalarField (k:=k)) →ₐ[ScalarField (k:=k)] W.RelativeRing :=
  MvPolynomial.rename some

theorem cutToRelative_X (i : Fin W.source.actualCutRank) :
    W.cutToRelative (MvPolynomial.X i)=MvPolynomial.X (some i) := MvPolynomial.rename_X _ _

theorem relativeToG_comp_cut : W.relativeToG.comp W.cutToRelative=W.cut.cutToG := by
  apply MvPolynomial.algHom_ext
  intro i
  dsimp only [AlgHom.comp_apply,cutToRelative,NumericalSemigroup.LinearCutData.cutToG]
  rw [MvPolynomial.rename_X,W.cut.toPolynomialRing_X,relativeToG_X_some]

noncomputable def algebraRestriction : ModuleCat (W.source.TangentAlgebra (ScalarField (k:=k))) ⥤ ModuleCat W.RelativeRing :=
  ModuleCat.restrictScalars W.relativeToG.toRingHom

noncomputable instance algebraRestriction_additive : W.algebraRestriction.Additive := by
  unfold algebraRestriction
  infer_instance

/-- A natural equality of the two actual restriction routes, retaining the
single fixed cut. It is valid for G, T, A and the image modules together. -/
noncomputable def cutRestrictionIso : W.cut.algebraRestriction ≅
    W.algebraRestriction ⋙ ModuleCat.restrictScalars W.cutToRelative.toRingHom :=
  ModuleCat.restrictScalarsComp' W.cutToRelative.toRingHom W.relativeToG.toRingHom W.cut.cutToG.toRingHom
    (by apply RingHom.ext;intro p;exact AlgHom.congr_fun W.relativeToG_comp_cut.symm p)

noncomputable def algebraRestrictionGIso :
    W.algebraRestriction.obj (W.source.algebraG (ScalarField (k:=k))) ≅ W.relativeG := by
  let e : W.algebraRestriction.obj (W.source.algebraG (ScalarField (k:=k))) ≃ₗ[W.RelativeRing] W.relativeG :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact e.toModuleIso
end NSP14.Ordinary.ActualWitness
