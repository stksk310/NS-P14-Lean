module
public import NSP14.ArithmeticSequence.ModelNativeReduction
public import NSP14.Homological.PolynomialAugmentation
public import NSP14.Homological.RegularAugmentationBetti
public import NSP14.Semigroup.AugmentationBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelVariablePolynomialEquiv :
    VariableRing k (Fin D.v) ≃ₐ[k] (D.ordinaryModel hv).source.FullPolynomialRing k :=
  MvPolynomial.renameEquiv k (D.modelFullAtomEquiv hv)

theorem modelVariablePolynomial_augmentation :
    (augmentation k (D.ordinaryModel hv).source.AtomExponent).comp
      (D.modelVariablePolynomialEquiv hv k).toAlgHom=augmentation k (Fin D.v) :=
  augmentation_rename k (Fin D.v) (D.ordinaryModel hv).source.AtomExponent (D.modelFullAtomEquiv hv)

theorem modelVariablePolynomial_presentation :
    ((D.ordinaryModel hv).source.fullPolynomialToG k).comp
      (D.modelVariablePolynomialEquiv hv k).toAlgHom=D.modelFullPolynomial hv k := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,modelVariablePolynomialEquiv,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  exact D.modelAtomPolynomial_X hv k i

theorem modelFullPolynomial_surjective : Function.Surjective (D.modelFullPolynomial hv k) := by
  have hs := ((D.ordinaryModel hv).source.fullPolynomialToG_surjective k).comp
    (D.modelVariablePolynomialEquiv hv k).surjective
  intro a
  obtain ⟨p,hp⟩ := hs a
  refine ⟨p,?_⟩
  exact (AlgHom.congr_fun (D.modelVariablePolynomial_presentation hv k) p).symm.trans hp

noncomputable def modelRegularFullIso :
    (ModuleCat.restrictScalars (D.modelVariablePolynomialEquiv hv k).toRingEquiv.toRingHom).obj
      (ModuleCat.of ((D.ordinaryModel hv).source.FullPolynomialRing k) ((D.ordinaryModel hv).source.TangentAlgebra k)) ≅
    D.modelFullRestricted hv k (ModuleCat.of ((D.ordinaryModel hv).source.TangentAlgebra k)
      ((D.ordinaryModel hv).source.TangentAlgebra k)) := by
  let e : (ModuleCat.restrictScalars (D.modelVariablePolynomialEquiv hv k).toRingEquiv.toRingHom).obj
      (ModuleCat.of ((D.ordinaryModel hv).source.FullPolynomialRing k) ((D.ordinaryModel hv).source.TangentAlgebra k)) ≃ₗ[VariableRing k (Fin D.v)]
    D.modelFullRestricted hv k (ModuleCat.of ((D.ordinaryModel hv).source.TangentAlgebra k)
      ((D.ordinaryModel hv).source.TangentAlgebra k)) :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' p a := by
        change (D.ordinaryModel hv).source.fullPolynomialToG k
          (D.modelVariablePolynomialEquiv hv k p)*(show (D.ordinaryModel hv).source.TangentAlgebra k from a)=
          D.modelFullPolynomial hv k p*(show (D.ordinaryModel hv).source.TangentAlgebra k from a)
        have h := AlgHom.congr_fun (D.modelVariablePolynomial_presentation hv k) p
        change (D.ordinaryModel hv).source.fullPolynomialToG k (D.modelVariablePolynomialEquiv hv k p)=D.modelFullPolynomial hv k p at h
        rw [h] }
  exact e.toModuleIso

noncomputable abbrev modelRegularNative : ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k) :=
  ModuleCat.of ((D.ordinaryModel hv).source.TangentAlgebra k) ((D.ordinaryModel hv).source.TangentAlgebra k)

noncomputable abbrev modelRegularFull : ModuleCat (VariableRing k (Fin D.v)) :=
  D.modelFullRestricted hv k (D.modelRegularNative hv k)

noncomputable instance modelRegularFullFinite :
    Module.Finite (VariableRing k (Fin D.v)) (D.modelRegularFull hv k) :=
  regularPresentation_finite k (Fin D.v) ((D.ordinaryModel hv).source.TangentAlgebra k)
    (D.modelFullPolynomial hv k) (D.modelFullPolynomial_surjective hv k)

theorem modelRegularFull_betti (i : ℕ) :
    totalBetti k (Fin D.v) (D.modelRegularFull hv k) i=
      totalBetti k (D.ordinaryModel hv).source.AtomExponent
        (ModuleCat.of ((D.ordinaryModel hv).source.FullPolynomialRing k)
          ((D.ordinaryModel hv).source.TangentAlgebra k)) i := by
  let := polynomialEquivRestricted_finite k (Fin D.v) (D.ordinaryModel hv).source.AtomExponent
    (D.modelVariablePolynomialEquiv hv k)
      (ModuleCat.of ((D.ordinaryModel hv).source.FullPolynomialRing k)
        ((D.ordinaryModel hv).source.TangentAlgebra k))
  have h := polynomialEquiv_totalBetti k (Fin D.v) (D.ordinaryModel hv).source.AtomExponent
    (D.modelVariablePolynomialEquiv hv k) (D.modelVariablePolynomial_augmentation hv k)
      (ModuleCat.of ((D.ordinaryModel hv).source.FullPolynomialRing k)
        ((D.ordinaryModel hv).source.TangentAlgebra k)) i
  exact (totalBetti_iso k (Fin D.v) (D.modelRegularFullIso hv k) i).symm.trans h

theorem modelRegularFull_betti_zero : totalBetti k (Fin D.v) (D.modelRegularFull hv k) 0=1 := by
  rw [D.modelRegularFull_betti]
  exact (D.ordinaryModel hv).source.actualG_totalBetti_zero k

theorem modelRegularFull_betti_pos (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (Fin D.v) (D.modelRegularFull hv k) i=i*D.v.choose (i+1) := by
  rw [D.modelRegularFull_betti]
  exact (D.ordinaryModel hv).maximalEmbedding_betti k rfl i hi
end NSP14.ArithmeticSequence.Data
