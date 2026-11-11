module
public import NSP14.Endpoint.SurvivingBasis
@[expose] public section
namespace NSP14.Endpoint.Data
theorem EndpointSurvivingBasis_acceptance_001 (D : Data) (k : Type) [Field k] (f : D.Core k) :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)) (D.coreToG k f)=0 ↔
      ∀ p,D.CoreMinimal p → D.coreDegree p=D.source.order (D.coreValue p).val → f.coeff p=0 :=
  D.actualEndpointQuotient_coeff_zero k f
end NSP14.Endpoint.Data
