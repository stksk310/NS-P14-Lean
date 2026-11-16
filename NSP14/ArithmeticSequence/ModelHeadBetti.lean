module
public import NSP14.ArithmeticSequence.ModelExactSequence
public import NSP14.Semigroup.RegularHeadBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelAPVariableEquiv : VariableRing k (Fin D.v) ≃ₐ[k] D.source.PolynomialRing k :=
  MvPolynomial.renameEquiv k D.nonXAtomIndexEquiv

theorem modelAPVariable_augmentation :
    (augmentation k D.source.NonXAtom).comp (D.modelAPVariableEquiv k).toAlgHom=augmentation k (Fin D.v) :=
  augmentation_rename k (Fin D.v) D.source.NonXAtom D.nonXAtomIndexEquiv

theorem modelAPVariable_presentation :
    (D.modelToHead hv k).comp (D.modelFullPolynomial hv k)=
      (D.source.polynomialToA k).comp (D.modelAPVariableEquiv k).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply,AlgHom.comp_apply,AlgEquiv.toAlgHom_apply,
    modelAPVariableEquiv,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,D.modelFullPolynomial_X]
  change D.modelToHeadLinear hv k (D.modelMonomial hv k (i.val+1))=_
  rw [D.modelToHeadLinear_monomial]
  exact (D.nonXAtomIndex_action k i).symm

noncomputable def modelAPHeadIso :
    (ModuleCat.restrictScalars (D.modelAPVariableEquiv k).toRingEquiv.toRingHom).obj
      (D.source.headPolynomialModule k) ≅ D.modelHeadFull hv k := by
  let e : (ModuleCat.restrictScalars (D.modelAPVariableEquiv k).toRingEquiv.toRingHom).obj
      (D.source.headPolynomialModule k) ≃ₗ[VariableRing k (Fin D.v)] D.modelHeadFull hv k :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' p a := by
        change D.source.polynomialToA k (D.modelAPVariableEquiv k p)*(show D.source.HeadAlgebra k from a)=
          D.modelToHead hv k (D.modelFullPolynomial hv k p)*(show D.source.HeadAlgebra k from a)
        have h := AlgHom.congr_fun (D.modelAPVariable_presentation hv k) p
        change D.modelToHead hv k (D.modelFullPolynomial hv k p)=
          D.source.polynomialToA k (D.modelAPVariableEquiv k p) at h
        rw [h] }
  exact e.toModuleIso

/-- The quotient in the auxiliary sequence computes exactly the Betti
numbers of the actual AP head over its own minimal non-x variables. -/
theorem modelHeadFull_betti (i : ℕ) :
    totalBetti k (Fin D.v) (D.modelHeadFull hv k) i=
      totalBetti k D.source.NonXAtom (D.source.headPolynomialModule k) i := by
  let := polynomialEquivRestricted_finite k (Fin D.v) D.source.NonXAtom
    (D.modelAPVariableEquiv k) (D.source.headPolynomialModule k)
  have h := polynomialEquiv_totalBetti k (Fin D.v) D.source.NonXAtom
    (D.modelAPVariableEquiv k) (D.modelAPVariable_augmentation k)
      (D.source.headPolynomialModule k) i
  exact (totalBetti_iso k (Fin D.v) (D.modelAPHeadIso hv k) i).symm.trans h

/-- Intrinsic full AP cone Tor equals the actual quotient Tor in the
same auxiliary sequence. -/
theorem apCone_betti_eq_modelHead (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=
      totalBetti k (Fin D.v) (D.modelHeadFull hv k) i := by
  rw [D.source.xRegular_totalBetti k (D.xMultiply_injective k),D.modelHeadFull_betti]
end NSP14.ArithmeticSequence.Data
