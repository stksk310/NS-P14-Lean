module
public import NSP14.Endpoint.Nilpotence
public import Mathlib.LinearAlgebra.Dimension.Finite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- Actual E-rank zero follows from the nonzero polynomial V^m which
annihilates every actual G element; coefficient finiteness is not used. -/
theorem actualEndpoint_rank_zero : Module.rank (D.EndpointRing k) (D.actualEndpointModule k)=0 := by
  apply rank_eq_zero_iff.mpr
  intro a
  refine ⟨(MvPolynomial.X (1 : Fin 2) : D.EndpointRing k)^D.m,
    pow_ne_zero D.m (MvPolynomial.X_ne_zero _),?_⟩
  change D.endpointToG k ((MvPolynomial.X (1 : Fin 2))^D.m)*(show D.source.TangentAlgebra k from a)=0
  rw [map_pow,D.endpoint_v_nilpotent,zero_mul]
end NSP14.Endpoint.Data
