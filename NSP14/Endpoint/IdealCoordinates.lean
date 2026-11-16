module
public import NSP14.Endpoint.KernelIdeals
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Module.Submodule.Equiv
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint
variable (k : Type) [Field k]

theorem coordinateIdeal_restrictScalars (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) :
    (coordinateIdeal k U).restrictScalars k=
      AddMonoidAlgebra.supported k k {b : Fin 2 →₀ ℕ | (b 0,b 1)∈U} := by
  ext f
  change f∈coordinateIdeal k U ↔ ∀ b,b∈f.support → (b 0,b 1)∈U
  exact coordinateIdeal_mem k U hU f

noncomputable def coordinateIdealCoefficients (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) :
    (coordinateIdeal k U) ≃ₗ[k] ({b : Fin 2 →₀ ℕ // (b 0,b 1)∈U} →₀ k) :=
  (LinearEquiv.ofEq _ _ (coordinateIdeal_restrictScalars k U hU)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R:=k) (S:=k) {b : Fin 2 →₀ ℕ | (b 0,b 1)∈U})
theorem coordinateIdealCoefficients_apply (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) (f : coordinateIdeal k U)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈U}) :
    coordinateIdealCoefficients k U hU f b=f.val.coeff b.val := rfl

end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def coreFiberCoefficients (r : Fin D.u) :
    (D.coreFiberIdeal k r) ≃ₗ[k] ({b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} →₀ k) :=
  NSP14.Endpoint.coordinateIdealCoefficients k (D.coreFiber r) (D.coreFiber_upward r)
theorem coreFiberCoefficients_apply (r : Fin D.u) (f : D.coreFiberIdeal k r)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    D.coreFiberCoefficients k r f b=f.val.coeff b.val := rfl

end NSP14.Endpoint.Data
