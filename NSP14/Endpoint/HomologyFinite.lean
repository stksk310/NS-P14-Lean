module
public import NSP14.Endpoint.FiberModule
public import NSP14.Homological.RegularActionCoefficient
public import NSP14.Homological.FullListBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- Ordered as v then x, so it is the actual v-cone on the actual
x-complex. The ordering is compared to ordinary E-Tor below. -/
noncomputable def endpointElements : List (D.source.TangentAlgebra k) :=
  [D.endpointToG k (MvPolynomial.X 1),D.endpointToG k (MvPolynomial.X 0)]

noncomputable def endpointComplex : ChainComplex (ModuleCat k) ℕ :=
  regularPartialCoefficientComplex k (D.source.TangentAlgebra k) (D.endpointElements k)

noncomputable def endpointPolynomialIso : D.endpointComplex k ≅
    (coefficientKoszulListFunctor k (Fin 2) [1,0]).obj (D.actualEndpointModule k) :=
  regularPartialPolynomialIso k (D.source.TangentAlgebra k) (Fin 2) (D.endpointToG k) [1,0]

noncomputable def endpointHomologyIso (i : ℕ) :
    (D.endpointComplex k).homology i ≅ koszulHomologyK k (Fin 2) (D.actualEndpointModule k) i :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (D.endpointPolynomialIso k) ≪≫
    (fullListHomologyKIso k (Fin 2) [1,0] (by intro x;fin_cases x <;> simp) (by decide)
      (D.actualEndpointModule k) i).symm

/-- Only homology is finite over k. The chain groups retain the actual
infinite-dimensional tangent algebra. -/
noncomputable instance endpointHomologyFinite (i : ℕ) :
    Module.Finite k ((D.endpointComplex k).homology i) := by
  let := koszul_homology_finite k (Fin 2) (D.actualEndpointModule k) i
  exact Module.Finite.equiv (D.endpointHomologyIso k i).symm.toLinearEquiv

theorem endpointHomology_betti (i : ℕ) :
    Module.finrank k ((D.endpointComplex k).homology i)=
      totalBetti k (Fin 2) (D.actualEndpointModule k) i :=
  (D.endpointHomologyIso k i).toLinearEquiv.finrank_eq

theorem endpointHomology_above (i : ℕ) (hi : 2 < i) :
    Module.finrank k ((D.endpointComplex k).homology i)=0 := by
  rw [D.endpointHomology_betti]
  exact totalBetti_eq_zero_of_gt k (Fin 2) _ i (by simpa using hi)
end NSP14.Endpoint.Data
