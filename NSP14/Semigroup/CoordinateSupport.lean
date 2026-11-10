module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

namespace NSP14

open scoped Classical

theorem supported_comap_eq_span {R I V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (e : V ≃ₗ[R] (I →₀ R)) (P : Set I) :
    (Finsupp.supported R R P).comap e.toLinearMap =
      Submodule.span R ((fun i => e.symm (Finsupp.single i 1)) '' P) := by
  have hm : (Finsupp.supported R R P).map e.symm.toLinearMap =
      Submodule.span R ((fun i => e.symm (Finsupp.single i 1)) '' P) := by
    rw [Finsupp.supported_eq_span_single,Submodule.map_span,Set.image_image]
    rfl
  rw [← hm]
  ext a
  constructor
  · intro ha
    exact ⟨e a,ha,e.symm_apply_apply a⟩
  · rintro ⟨f,hf,rfl⟩
    change e (e.symm f) ∈ Finsupp.supported R R P
    rw [LinearEquiv.apply_symm_apply]
    exact hf

end NSP14
