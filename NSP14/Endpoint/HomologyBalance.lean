module
public import NSP14.Endpoint.XHomology
public import NSP14.Endpoint.ConeBalance
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def vOnXComplex : D.xComplex k ⟶ D.xComplex k :=
  (nativeCoefficientFunctor k (D.source.TangentAlgebra k)).map
    (D.endpointToG k (MvPolynomial.X 1) • 𝟙 (D.xNativeComplex k))

noncomputable def endpointConeIso : D.endpointComplex k ≅ homotopyCofiber (D.vOnXComplex k) := by
  unfold endpointComplex endpointElements regularPartialCoefficientComplex
  rw [D.endpoint_xElement]
  exact homotopyCofiber.mapHomologicalComplexObjIso _
    (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k)))

/-- Exact three-row Euler identity from the actual x-kernel/head and
the actual v-cone. In particular finrank(G) is never evaluated. -/
theorem endpointHomology_balance :
    Module.finrank k ((D.endpointComplex k).homology 1)=
      Module.finrank k ((D.endpointComplex k).homology 0)+
        Module.finrank k ((D.endpointComplex k).homology 2) := by
  have hz : Module.finrank k ((D.xComplex k).homology 2)=0 := by
    have : Subsingleton ((D.xComplex k).homology 2) :=
      ModuleCat.subsingleton_of_isZero (D.xHomology_above k 2 (by omega))
    exact Module.finrank_zero_of_subsingleton
  have h := NSP14.Endpoint.endomorphismCone_balance k (D.xComplex k) (D.vOnXComplex k) hz
  have he (i : ℕ) : Module.finrank k ((D.endpointComplex k).homology i)=
      Module.finrank k ((homotopyCofiber (D.vOnXComplex k)).homology i) :=
    ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (D.endpointConeIso k)).toLinearEquiv.finrank_eq
  rw [←he 0,←he 1,←he 2] at h
  exact h
end NSP14.Endpoint.Data
