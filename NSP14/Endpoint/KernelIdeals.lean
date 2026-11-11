module
public import NSP14.Endpoint.ActualKernel
public import NSP14.Endpoint.CoordinateIdeals
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem actualDeadFiber_upward (s : Fin D.u) {a b : ℕ×ℕ}
    (ha : a∈D.actualDeadFiber s) (hab : a≤b) : b∈D.actualDeadFiber s := by
  rw [D.actualDeadFiber_eq_inter] at ha ⊢
  exact ⟨D.coreFiber_upward s ha.1 hab,D.competitorFiber_upward s ha.2 hab⟩

variable (k : Type) [Field k]
noncomputable def competitorIdeal (s : Fin D.u) : Ideal (D.EndpointRing k) :=
  NSP14.Endpoint.coordinateIdeal k (D.competitorFiber s)

/-- Defined by the actual order-killed core exponents, independently of
the forbidden-region ideal. The intersection equality is proved below. -/
noncomputable def actualKernelIdeal (s : Fin D.u) : Ideal (D.EndpointRing k) :=
  NSP14.Endpoint.coordinateIdeal k (D.actualDeadFiber s)

theorem actualKernelIdeal_eq_inf (s : Fin D.u) :
    D.actualKernelIdeal k s=D.coreFiberIdeal k s⊓D.competitorIdeal k s := by
  change NSP14.Endpoint.coordinateIdeal k (D.actualDeadFiber s)=_
  rw [D.actualDeadFiber_eq_inter,NSP14.Endpoint.coordinateIdeal_inter k _ _
    (D.coreFiber_upward s) (D.competitorFiber_upward s)]
  rfl

theorem actualKernelIdeal_mem (s : Fin D.u) (f : D.EndpointRing k) :
    f∈D.actualKernelIdeal k s ↔ ∀ b∈f.support,(b 0,b 1)∈D.actualDeadFiber s :=
  NSP14.Endpoint.coordinateIdeal_mem k (D.actualDeadFiber s) (D.actualDeadFiber_upward s) f
end NSP14.Endpoint.Data
