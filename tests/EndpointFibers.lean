module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointFibersAcceptance
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem upward (r : Fin D.u) (a b : ℕ×ℕ) (ha : a∈D.coreFiber r) (hab : a≤b) : b∈D.coreFiber r :=
  D.coreFiber_upward r ha hab

theorem zero_ideal : D.coreFiberIdeal k ⟨0,D.u_pos⟩=⊤ := D.coreFiberIdeal_zero k
end EndpointFibersAcceptance

namespace EndpointFibersAcceptance
open NSP14
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_ideal_coefficients (r : Fin D.u) :
    Nonempty ((D.coreFiberIdeal k r) ≃ₗ[k]
      ({b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} →₀ k)) :=
  ⟨D.coreFiberCoefficients k r⟩
end EndpointFibersAcceptance

namespace EndpointFibersAcceptance
open NSP14
variable (D : Endpoint.Data) (k : Type) [Field k]
theorem actual_coefficient_value (r : Fin D.u) (f : D.coreFiberIdeal k r)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    D.coreFiberCoefficients k r f b=f.val.coeff b.val :=
  D.coreFiberCoefficients_apply k r f b
end EndpointFibersAcceptance
