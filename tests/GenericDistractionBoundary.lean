module
public import NSP14.Lex.GenericDistractionBoundary
public import NSP14.Homological.KoszulExterior
@[expose] public section
open scoped Classical TensorProduct BigOperators
open CategoryTheory NSP14.Homological
namespace NSP14.Tests.GenericDistractionBoundary
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_generic_boundary (M : ModuleCat (VariableRing K (Fin q))) {J : Type}
    (b : Module.Basis J K (coefficientModule K (Fin q) M)) (j : ℕ) (a : Fin q →₀ ℕ)
    (m : coefficientModule K (Fin q) M) (w : ⋀[K]^(j+1) (Fin q → K)) :
    koszulExteriorBoundary K (Fin q) M b j
      ((Lex.genericFieldDistraction k q a • m) ⊗ₜ[K] Lex.genericDistractionWedgeEquiv k q (j+1) a w)=
      ∑ i : Fin q, (Lex.genericFieldDistraction k q (a+Finsupp.single i 1) • m) ⊗ₜ[K]
        Lex.genericDistractionWedgeEquiv k q j (a+Finsupp.single i 1)
          (koszulExteriorContraction K (Fin q) j (LinearMap.proj i) w) :=
  Lex.genericDistractionBoundary_monomial k q M b j a m w
end NSP14.Tests.GenericDistractionBoundary
