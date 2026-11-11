module
public import NSP14.Endpoint.ConeBalance
public import NSP14.Homological.EndomorphismConeBound
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Endpoint
variable (k : Type) [Field k] (K : ChainComplex (ModuleCat.{0} k) ℕ) (f : K ⟶ K)
  [∀ i,Module.Finite k (K.homology i)]
theorem EndpointConeBalance_acceptance_001 (h : Module.finrank k (K.homology 2)=0) :
    Module.finrank k ((homotopyCofiber f).homology 1)=
      Module.finrank k ((homotopyCofiber f).homology 0)+Module.finrank k ((homotopyCofiber f).homology 2) :=
  endomorphismCone_balance k K f h
end NSP14.Endpoint
