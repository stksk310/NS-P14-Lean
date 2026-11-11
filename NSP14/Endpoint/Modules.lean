module
public import NSP14.Endpoint.CoreMap
public import NSP14.Homological.RegularRestriction
public import NSP14.Homological.PolynomialLinearMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def endpointToCore : D.EndpointRing k →ₐ[k] D.Core k :=
  (D.fullToCore k).comp (D.endpointToFull k)

theorem endpointToCore_X (i : Fin 2) :
    D.endpointToCore k (MvPolynomial.X i)=D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i)) := by
  simp only [endpointToCore,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X,
    fullToCore,MvPolynomial.aeval_X]

theorem coreToG_endpointToCore : (D.coreToG k).comp (D.endpointToCore k)=D.endpointToG k := by
  rw [endpointToCore,← AlgHom.comp_assoc,D.coreToG_fullToCore]
  rfl

/-- The actual actions are attached to module objects, keeping other
Fin-2 cut actions on the same G out of the typeclass instance search. -/
noncomputable def coreEndpointModule : ModuleCat (D.EndpointRing k) :=
  polynomialRegularModule k (Fin 2) (D.Core k) (D.endpointToCore k)

noncomputable def actualEndpointModule : ModuleCat (D.EndpointRing k) :=
  polynomialRegularModule k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def coreEndpointCoefficients :
    coefficientModule k (Fin 2) (D.coreEndpointModule k) ≃ₗ[k] D.Core k :=
  regularRestrictionCoefficientEquiv k (Fin 2) (D.Core k) (D.endpointToCore k)

noncomputable def actualEndpointCoefficients :
    coefficientModule k (Fin 2) (D.actualEndpointModule k) ≃ₗ[k] D.source.TangentAlgebra k :=
  regularRestrictionCoefficientEquiv k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def coreToGEndpoint : D.coreEndpointModule k ⟶ D.actualEndpointModule k :=
  ModuleCat.ofHom (X:=D.coreEndpointModule k) (Y:=D.actualEndpointModule k) {
    toFun a := D.coreToG k (show D.Core k from a)
    map_add' a b := (D.coreToG k).map_add a b
    map_smul' p a := by
      change D.coreToG k (D.endpointToCore k p*(show D.Core k from a))=
        D.endpointToG k p*D.coreToG k (show D.Core k from a)
      rw [map_mul]
      have h := AlgHom.congr_fun (D.coreToG_endpointToCore k) p
      change D.coreToG k (D.endpointToCore k p)=D.endpointToG k p at h
      rw [h] }

theorem coreToGEndpoint_surjective : Function.Surjective (D.coreToGEndpoint k).hom := by
  intro a
  obtain ⟨b,hb⟩ := D.coreToG_surjective k (show D.source.TangentAlgebra k from a)
  exact ⟨b,hb⟩

theorem coreEndpoint_variable (i : Fin 2) (a : coefficientModule k (Fin 2) (D.coreEndpointModule k)) :
    D.coreEndpointCoefficients k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreEndpointCoefficients k a := by
  change D.endpointToCore k (MvPolynomial.X i)*(show D.Core k from a)=_
  rw [D.endpointToCore_X]
  rfl
end NSP14.Endpoint.Data
