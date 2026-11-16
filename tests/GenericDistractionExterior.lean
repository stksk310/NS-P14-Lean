module
public import NSP14.Lex.GenericDistractionExterior
public import NSP14.Homological.KoszulExteriorMap
@[expose] public section
open scoped Classical
open NSP14.Homological
namespace NSP14.Tests.GenericDistractionExterior
theorem actual_generic_shift_after_contraction (k : Type) [Field k] (q j : ℕ)
    (a : Fin q →₀ ℕ) (i : Fin q)
    (w : ⋀[Lex.GenericDistractionField k q]^(j+1) (Fin q → Lex.GenericDistractionField k q)) :
    exteriorPowerLinearEquiv (Lex.GenericDistractionField k q) j (Lex.genericFieldLinearEquiv k q a)
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w)=
    exteriorPowerLinearEquiv (Lex.GenericDistractionField k q) j
      (Lex.genericFieldLinearEquiv k q (a+Finsupp.single i 1))
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w) :=
  Lex.genericDistractionWedge_step_contraction k q j a i w
end NSP14.Tests.GenericDistractionExterior
