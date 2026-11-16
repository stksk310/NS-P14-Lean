module
public import NSP14.Endpoint.FiberIndices
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint
variable (k : Type) [Field k]

theorem coordinateIdealCoefficients_symm_single (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈U}) :
    ((coordinateIdealCoefficients k U hU).symm (Finsupp.single b 1)).val=
      MvPolynomial.monomial b.val (1:k) := by
  apply (AddMonoidAlgebra.coeffLinearEquiv k).injective
  change ((Finsupp.supportedEquivFinsupp (R:=k) {b : Fin 2 →₀ ℕ | (b 0,b 1)∈U}).symm
    (Finsupp.single b (1:k))).val=Finsupp.single b.val (1:k)
  exact Finsupp.supportedEquivFinsupp_symm_single {b : Fin 2 →₀ ℕ | (b 0,b 1)∈U} b (1:k)

noncomputable def coordinateIdealBasis (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U) :
    Module.Basis {b : Fin 2 →₀ ℕ // (b 0,b 1)∈U} k (coordinateIdeal k U) :=
  Finsupp.basisSingleOne.map (coordinateIdealCoefficients k U hU).symm

theorem coordinateIdealBasis_val (U : Set (ℕ×ℕ))
    (hU : ∀ {a b},a∈U → a≤b → b∈U)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈U}) :
    (coordinateIdealBasis k U hU b).val=MvPolynomial.monomial b.val (1:k) := by
  rw [coordinateIdealBasis,Module.Basis.map_apply]
  change ((coordinateIdealCoefficients k U hU).symm (Finsupp.single b (1:k))).val=_
  exact coordinateIdealCoefficients_symm_single k U hU b
end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def coreFiberBasis (r : Fin D.u) :
    Module.Basis {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} k (D.coreFiberIdeal k r) :=
  NSP14.Endpoint.coordinateIdealBasis k (D.coreFiber r) (D.coreFiber_upward r)

theorem coreFiberBasis_val (r : Fin D.u)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    (D.coreFiberBasis k r b).val=MvPolynomial.monomial b.val (1:k) :=
  NSP14.Endpoint.coordinateIdealBasis_val k (D.coreFiber r) (D.coreFiber_upward r) b
end NSP14.Endpoint.Data
