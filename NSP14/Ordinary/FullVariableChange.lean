module
public import NSP14.Homological.OptionPolynomialEquiv
public import NSP14.Homological.PolynomialAugmentation
public import NSP14.Semigroup.AtomSplit
public import NSP14.Ordinary.NativeCutH0Z
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- The chosen actual x and the same extended non-x basis give an
invertible change of the full minimal polynomial presentation. -/
noncomputable def extendedFullPolynomialEquiv :
    VariableRing k (Option (Fin (S.actualCutRank+C.complementRank))) ≃ₐ[k] S.FullPolynomialRing k :=
  (optionPolynomialEquiv k _ _ C.extendedPolynomialEquiv).trans
    (MvPolynomial.renameEquiv k S.optionNonXAtomEquiv)

theorem extendedFullPolynomialEquiv_none : C.extendedFullPolynomialEquiv (MvPolynomial.X none)=
    MvPolynomial.X (⟨S.multiplicityExponent,S.multiplicity_atom⟩ : S.AtomExponent) := by
  change MvPolynomial.rename S.optionNonXAtomEquiv (optionPolynomialEquiv k _ _ C.extendedPolynomialEquiv (MvPolynomial.X none))=_
  rw [optionPolynomialEquiv_X_none,MvPolynomial.rename_X]
  rfl

theorem extendedFullPolynomialEquiv_some (i : Fin (S.actualCutRank+C.complementRank)) :
    C.extendedFullPolynomialEquiv (MvPolynomial.X (some i))=
      S.nonXPolynomialInclusion k (C.extendedPolynomialEquiv (MvPolynomial.X i)) := by
  change MvPolynomial.rename S.optionNonXAtomEquiv (optionPolynomialEquiv k _ _ C.extendedPolynomialEquiv (MvPolynomial.X (some i)))=_
  rw [optionPolynomialEquiv_X_some,MvPolynomial.rename_rename]
  rfl

theorem extendedFullPolynomialEquiv_augmentation :
    (augmentation k S.AtomExponent).comp C.extendedFullPolynomialEquiv.toAlgHom=
      augmentation k (Option (Fin (S.actualCutRank+C.complementRank))) := by
  have hi : (augmentation k S.AtomExponent).comp (S.nonXPolynomialInclusion k)=augmentation k S.NonXAtom :=
    augmentation_rename k _ _ _
  have hc : (augmentation k S.NonXAtom).comp C.extendedPolynomialEquiv.toAlgHom=
      augmentation k (Fin (S.actualCutRank+C.complementRank)) :=
    polynomialLinearEquiv_augmentation k _ _ C.extendedCoefficientEquiv
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none =>
    change augmentation k S.AtomExponent (C.extendedFullPolynomialEquiv (MvPolynomial.X none))=_
    rw [C.extendedFullPolynomialEquiv_none]
    simp only [augmentation_X]
  | some i =>
    change augmentation k S.AtomExponent (C.extendedFullPolynomialEquiv (MvPolynomial.X (some i)))=_
    rw [C.extendedFullPolynomialEquiv_some,augmentation_X]
    calc
      _ = augmentation k S.NonXAtom (C.extendedPolynomialEquiv (MvPolynomial.X i)) := AlgHom.congr_fun hi _
      _ = augmentation k (Fin (S.actualCutRank+C.complementRank)) (MvPolynomial.X i) := AlgHom.congr_fun hc _
      _ = 0 := augmentation_X _ _ _

noncomputable def extendedFullToG :
    VariableRing k (Option (Fin (S.actualCutRank+C.complementRank))) →ₐ[k] S.TangentAlgebra k :=
  (S.fullPolynomialToG k).comp C.extendedFullPolynomialEquiv.toAlgHom

theorem extendedFullToG_none : C.extendedFullToG (MvPolynomial.X none)=S.xElement k := by
  change S.fullPolynomialToG k (C.extendedFullPolynomialEquiv (MvPolynomial.X none))=_
  rw [C.extendedFullPolynomialEquiv_none,S.fullPolynomialToG_X]
  rfl

theorem extendedFullToG_some (i : Fin (S.actualCutRank+C.complementRank)) :
    C.extendedFullToG (MvPolynomial.X (some i))=C.extendedPolynomialToG (MvPolynomial.X i) := by
  change S.fullPolynomialToG k (C.extendedFullPolynomialEquiv (MvPolynomial.X (some i)))=_
  rw [C.extendedFullPolynomialEquiv_some]
  exact AlgHom.congr_fun (S.fullPolynomial_nonX_compat k) _
end NSP14.NumericalSemigroup.LinearCutData
