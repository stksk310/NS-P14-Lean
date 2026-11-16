module
public import NSP14.Endpoint.ArtinQuotient
public import NSP14.Endpoint.MinimalPredecessors
public import Mathlib.Algebra.MonoidAlgebra.Ideal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreEndpointIdeal_generators :
    {a : D.Core k | a∈[D.endpointToCore k (MvPolynomial.X 1),D.endpointToCore k (MvPolynomial.X 0)]}=
      AddMonoidAlgebra.of' k D.corePoints '' {D.coreGeneratorPoint D.xVariable,D.coreGeneratorPoint D.vVariable} := by
  rw [Set.image_insert_eq,Set.image_singleton]
  ext a
  simp only [Set.mem_ofPred_eq,List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,
    D.endpointToCore_X]
  change (a=D.coreMonomial k (D.coreGeneratorPoint D.vVariable) ∨ a=D.coreMonomial k (D.coreGeneratorPoint D.xVariable)) ↔
    (a=D.coreMonomial k (D.coreGeneratorPoint D.xVariable) ∨ a=D.coreMonomial k (D.coreGeneratorPoint D.vVariable))
  exact or_comm

/-- The actual endpoint ideal kills exactly nonminimal core monomials,
so arbitrary linear combinations have the expected quotient kernel. -/
theorem coreEndpointIdeal_mem (f : D.Core k) :
    f∈NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k) ↔
      ∀ p∈f.coeff.support,¬D.CoreMinimal p := by
  rw [NSP14.Endpoint.endpointIdeal,D.coreEndpointIdeal_generators,AddMonoidAlgebra.mem_ideal_span_of'_image]
  constructor
  · intro h p hp
    obtain ⟨b,hb,q,hq⟩ := h p hp
    apply (D.core_not_minimal_iff_factor p).mpr
    rcases (show b=D.coreGeneratorPoint D.xVariable ∨ b=D.coreGeneratorPoint D.vVariable by simpa using hb) with rfl|rfl
    · exact Or.inl ⟨q,hq⟩
    · exact Or.inr ⟨q,hq⟩
  · intro h p hp
    rcases (D.core_not_minimal_iff_factor p).mp (h p hp) with ⟨q,hq⟩|⟨q,hq⟩
    · exact ⟨D.coreGeneratorPoint D.xVariable,by simp,q,hq⟩
    · exact ⟨D.coreGeneratorPoint D.vVariable,by simp,q,hq⟩

theorem coreEndpointIdeal_coeff_zero (f : D.Core k) :
    f∈NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k) ↔
      ∀ p,D.CoreMinimal p → f.coeff p=0 := by
  rw [D.coreEndpointIdeal_mem]
  constructor
  · intro h p hp
    by_contra hne
    exact h p (Finsupp.mem_support_iff.mpr hne) hp
  · intro h p hp hmin
    exact (Finsupp.mem_support_iff.mp hp) (h p hmin)
end NSP14.Endpoint.Data
