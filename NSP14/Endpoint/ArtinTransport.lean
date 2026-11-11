module
public import NSP14.Endpoint.ArtinQuotient
public import NSP14.Endpoint.HomologyBalance
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable instance QCoreFinite : Module.Finite k (D.QCore k) := by
  let : Module.Finite (D.EndpointRing k)
      (polynomialRegularModule k (Fin 2) (D.Core k) (D.endpointToCore k)) := D.coreEndpointFinite k
  exact NSP14.Endpoint.endpointQuotientFinite k (D.Core k) (D.endpointToCore k)

noncomputable instance QActualFinite : Module.Finite k (D.QActual k) := by
  let : Module.Finite (D.EndpointRing k)
      (polynomialRegularModule k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)) := D.actualEndpointFinite k
  exact NSP14.Endpoint.endpointQuotientFinite k (D.source.TangentAlgebra k) (D.endpointToG k)

theorem core_endpointIdeal_le : NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k)≤
    Ideal.comap (D.coreToG k) (NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)) := by
  apply Ideal.span_le.mpr
  intro a ha
  change D.coreToG k a∈NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)
  have he (i : Fin 2) : D.coreToG k (D.endpointToCore k (MvPolynomial.X i))=D.endpointToG k (MvPolynomial.X i) :=
    AlgHom.congr_fun (D.coreToG_endpointToCore k) (MvPolynomial.X i)
  rcases (show a=D.endpointToCore k (MvPolynomial.X 1) ∨ a=D.endpointToCore k (MvPolynomial.X 0) by
    simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,Set.mem_ofPred_eq] using ha) with rfl|rfl
  · rw [he]
    exact Ideal.subset_span (by simp)
  · rw [he]
    exact Ideal.subset_span (by simp)

/-- The genuine quotient map QC -> QG of the same core-to-G map. -/
noncomputable def QCoreToActual : D.QCore k →ₐ[k] D.QActual k :=
  Ideal.quotientMapₐ _ (D.coreToG k) (D.core_endpointIdeal_le k)

theorem QCoreToActual_surjective : Function.Surjective (D.QCoreToActual k) :=
  Ideal.quotientMap_surjective (H:=D.core_endpointIdeal_le k) (D.coreToG_surjective k)

noncomputable def internalToCore : D.InternalRing k →ₐ[k] D.Core k :=
  (D.fullToCore k).comp (D.internalToFull k)

noncomputable def internalToQCore : D.InternalRing k →ₐ[k] D.QCore k :=
  (Ideal.Quotient.mkₐ k _).comp (D.internalToCore k)

noncomputable def internalToQActual : D.InternalRing k →ₐ[k] D.QActual k :=
  (Ideal.Quotient.mkₐ k _).comp (D.internalToG k)

noncomputable def QCoreModule : ModuleCat (D.InternalRing k) :=
  polynomialRegularModule k D.a (D.QCore k) (D.internalToQCore k)

noncomputable def QActualModule : ModuleCat (D.InternalRing k) :=
  polynomialRegularModule k D.a (D.QActual k) (D.internalToQActual k)

noncomputable instance QCoreModuleFinite : Module.Finite (D.InternalRing k) (D.QCoreModule k) :=
  regularRestriction_finite k D.a _ _

noncomputable instance QActualModuleFinite : Module.Finite (D.InternalRing k) (D.QActualModule k) :=
  regularRestriction_finite k D.a _ _

theorem QCoreToActual_internal (p : D.InternalRing k) :
    D.QCoreToActual k (D.internalToQCore k p)=D.internalToQActual k p := by
  change Ideal.Quotient.mk _ (D.coreToG k (D.fullToCore k (D.internalToFull k p)))=
    Ideal.Quotient.mk _ (D.fullToG k (D.internalToFull k p))
  have he := AlgHom.congr_fun (D.coreToG_fullToCore k) (D.internalToFull k p)
  exact congrArg (Ideal.Quotient.mk _) he

noncomputable def QCoreToActualModule : D.QCoreModule k ⟶ D.QActualModule k :=
  ModuleCat.ofHom (X:=D.QCoreModule k) (Y:=D.QActualModule k) {
    toFun a := D.QCoreToActual k (show D.QCore k from a)
    map_add' a b := (D.QCoreToActual k).map_add a b
    map_smul' p a := by
      change D.QCoreToActual k (D.internalToQCore k p*(show D.QCore k from a))=
        D.internalToQActual k p*D.QCoreToActual k (show D.QCore k from a)
      rw [map_mul,D.QCoreToActual_internal] }

theorem actualH1_dimension : Module.finrank k ((D.endpointComplex k).homology 1)=D.actualP k+D.actualR k := by
  rw [D.endpointHomology_balance,D.actualH0_dimension]
  rfl
end NSP14.Endpoint.Data
