module
public import NSP14
@[expose] public section
open NSP14 NSP14.Homological
namespace EndpointPresentationAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem full_count : Fintype.card D.Variables=D.q+2 := D.variables_card

theorem actual_ring : Nonempty (D.FullRing k ≃ₐ[k] D.source.FullPolynomialRing k) :=
  ⟨D.fullPolynomialEquiv k⟩

theorem endpoint_count : Fintype.card (Fin 2)=2 := Fintype.card_fin 2

theorem internal_count : Fintype.card D.a=D.q := by simp only [Fintype.card_coe];rfl
end EndpointPresentationAcceptance
