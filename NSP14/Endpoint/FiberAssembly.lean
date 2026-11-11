module
public import NSP14.Endpoint.IdealBasis
public import NSP14.Endpoint.Modules
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

abbrev FiberBasisIndex := Σ r : Fin D.u,{b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}

noncomputable def fiberPolynomialIndexEquiv : D.FiberBasisIndex ≃ D.corePoints :=
  (Equiv.sigmaCongrRight (fun r => D.fiberExponentEquiv r)).trans
    (D.coordinateFiberEquiv.symm.trans D.coreCoordinateEquiv.symm)

def fiberPolynomialPoint (r : Fin D.u)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) : D.corePoints :=
  ⟨D.decodeCoordinate (r,(b.val 0,b.val 1)),b.property⟩

theorem fiberPolynomialIndexEquiv_apply (b : D.FiberBasisIndex) :
    D.fiberPolynomialIndexEquiv b=D.fiberPolynomialPoint b.1 b.2 := rfl

variable (k : Type) [Field k]
noncomputable def coreSumBasis : Module.Basis D.FiberBasisIndex k (⨁ r : Fin D.u,D.coreFiberIdeal k r) :=
  DFinsupp.basis (fun r => D.coreFiberBasis k r)

theorem coreSumBasis_apply (b : D.FiberBasisIndex) :
    D.coreSumBasis k b=DFinsupp.single b.1 (D.coreFiberBasis k b.1 b.2) := by
  apply (D.coreSumBasis k).repr.injective
  rw [Module.Basis.repr_self]
  symm
  change (sigmaFinsuppLequivDFinsupp k).symm
    (DFinsupp.mapRange (fun r a => (D.coreFiberBasis k r).repr a)
      (fun r => (D.coreFiberBasis k r).repr.map_zero)
      (DFinsupp.single b.1 (D.coreFiberBasis k b.1 b.2)))=Finsupp.single b 1
  rw [DFinsupp.mapRange_single,Module.Basis.repr_self]
  apply (sigmaFinsuppLequivDFinsupp k).symm_apply_eq.mpr
  exact (sigmaFinsuppEquivDFinsupp_single b (1:k)).symm

/-- The actual monomial-basis assembly before polynomial-linearity is
proved. Its source is a direct sum of genuine polynomial ideals. -/
noncomputable def coreFiberLinearAssembly : (⨁ r : Fin D.u,D.coreFiberIdeal k r) ≃ₗ[k] D.Core k :=
  (D.coreSumBasis k).equiv (AddMonoidAlgebra.basis D.corePoints k) D.fiberPolynomialIndexEquiv

theorem coreFiberLinearAssembly_basis (b : D.FiberBasisIndex) :
    D.coreFiberLinearAssembly k (D.coreSumBasis k b)=D.coreMonomial k (D.fiberPolynomialPoint b.1 b.2) := by
  rw [coreFiberLinearAssembly,Module.Basis.equiv_apply,D.fiberPolynomialIndexEquiv_apply]
  rfl
end NSP14.Endpoint.Data
