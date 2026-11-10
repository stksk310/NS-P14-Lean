module

public import NSP14.Green.CutImage

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.Green

variable {k V W ι : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [Fintype ι]

noncomputable def formProductMap (μ : V →ₗ[k] V →ₗ[k] W) (c : ι → V) : (ι → V) →ₗ[k] W where
  toFun a := ∑ i, μ (c i) (a i)
  map_add' a b := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

theorem formProductMap_single (μ : V →ₗ[k] V →ₗ[k] W) (c : ι → V) (i : ι) (a : V) :
    formProductMap μ c (Pi.single i a) = μ (c i) a := by
  change (∑ j, μ (c j) ((Pi.single i a : ι → V) j)) = _
  simp [Pi.single,Function.update_apply,apply_ite]

/-- The span-of-forms quadratic image is the range of an actual finite product map. -/
theorem formProductMap_range (μ : V →ₗ[k] V →ₗ[k] W) (c : ι → V) :
    (formProductMap μ c).range = cutImage μ (Submodule.span k (Set.range c)) := by
  apply le_antisymm
  · rintro a ⟨v,rfl⟩
    change (∑ i, μ (c i) (v i)) ∈ _
    apply Submodule.sum_mem
    intro i _
    exact product_mem_cutImage μ (Submodule.span k (Set.range c)) (c i)
      (Submodule.subset_span ⟨i,rfl⟩) (v i)
  · apply Submodule.span_le.mpr
    rintro a ⟨x,hx,y,rfl⟩
    have hspan : Submodule.span k (Set.range c) ≤ (formProductMap μ c).range.comap (μ.flip y) := by
      apply Submodule.span_le.mpr
      rintro z ⟨i,rfl⟩
      exact ⟨Pi.single i y,formProductMap_single μ c i y⟩
    exact hspan hx

theorem formProductMap_surjective (μ : V →ₗ[k] V →ₗ[k] W) (c : ι → V)
    (h : cutImage μ (Submodule.span k (Set.range c)) = ⊤) :
    Function.Surjective (formProductMap μ c) := by
  rw [← LinearMap.range_eq_top,formProductMap_range,h]

end NSP14.Green
