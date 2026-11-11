module
public import NSP14.Endpoint.CoreInternalPresentation
public import NSP14.Endpoint.FullTransfer
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem fullToG_augmentation_X (b : D.Variables) :
    D.source.tangentAugmentation k (D.fullToG k (MvPolynomial.X b))=0 := by
  have h := AlgHom.congr_fun (D.source.tangentAugmentation_polynomial k) (MvPolynomial.X (D.atomVariable b))
  change D.source.tangentAugmentation k (D.source.fullPolynomialToG k (MvPolynomial.X (D.atomVariable b)))=_ at h
  rw [D.source.fullPolynomialToG_X,augmentation_X] at h
  rw [D.fullToG_X]
  exact h

theorem actual_endpointIdeal_augmentation :
    NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)≤
      RingHom.ker (D.source.tangentAugmentation k).toRingHom := by
  apply Ideal.span_le.mpr
  intro a ha
  have he (i : Fin 2) : D.source.tangentAugmentation k (D.endpointToG k (MvPolynomial.X i))=0 := by
    simp only [endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
    exact D.fullToG_augmentation_X k _
  rcases (show a=D.endpointToG k (MvPolynomial.X 1) ∨ a=D.endpointToG k (MvPolynomial.X 0) by simpa using ha) with rfl|rfl
  · exact he 1
  · exact he 0

noncomputable def QActualAugmentation : D.QActual k →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (D.source.tangentAugmentation k) (D.actual_endpointIdeal_augmentation k)

noncomputable def QCoreAugmentation : D.QCore k →ₐ[k] k := (D.QActualAugmentation k).comp (D.QCoreToActual k)

theorem QCore_augmentation_polynomial : (D.QCoreAugmentation k).comp (D.internalToQCore k)=augmentation k D.a := by
  apply MvPolynomial.algHom_ext
  intro b
  change D.QActualAugmentation k (D.QCoreToActual k (D.internalToQCore k (MvPolynomial.X b)))=_
  rw [D.QCoreToActual_internal]
  change D.source.tangentAugmentation k (D.internalToG k (MvPolynomial.X b))=augmentation k D.a (MvPolynomial.X b)
  rw [augmentation_X]
  simp only [internalToG,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X]
  exact D.fullToG_augmentation_X k _

theorem QCore_betti_zero : totalBetti k D.a (D.QCoreModule k) 0=1 :=
  regularAugmented_totalBetti_zero k D.a (D.QCore k) (D.internalToQCore k) (D.QCoreAugmentation k)
    (D.internalToQCore_surjective k) (D.QCore_augmentation_polynomial k)
end NSP14.Endpoint.Data
