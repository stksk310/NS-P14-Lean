module
public import NSP14.Endpoint.CoreRelations
public import NSP14.Endpoint.FiniteMinima
@[expose] public section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace EndpointNonmonomialAcceptance
open NSP14

def D : Endpoint.Data where
  m := 9
  d := 1
  u := 7
  a := {2,3,4}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def a : D.a := ⟨2,by decide⟩
def b : D.a := ⟨3,by decide⟩
def c : D.a := ⟨4,by decide⟩
variable (k : Type) [Field k]
theorem EndpointNonmonomial_acceptance_001 : D.internalToQCore k (MvPolynomial.X a)*D.internalToQCore k (MvPolynomial.X c)=
    D.internalToQCore k (MvPolynomial.X b)*D.internalToQCore k (MvPolynomial.X b) :=
  D.QCore_quadratic_relation k a c b b (by decide)

theorem EndpointNonmonomial_acceptance_002 : D.internalToQCore k (MvPolynomial.X a)*D.internalToQCore k (MvPolynomial.X c)≠0 := by
  let p := D.coreGeneratorPoint (D.internalVariable a)+D.coreGeneratorPoint (D.internalVariable c)
  have hp : D.CoreMinimal p := by
    unfold Endpoint.Data.CoreMinimal
    have he : D.coreCoordinates p=(⟨6,by decide⟩,1,0) := by decide
    rw [he]
    exact (D.computedMinima_iff _ _).mp (by decide)
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X a))*
    Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X c))≠0
  rw [←map_mul,D.internalToCore_X,D.internalToCore_X,D.coreMonomial_mul]
  exact D.QCore_minimal_monomial_nonzero k p hp
end EndpointNonmonomialAcceptance
