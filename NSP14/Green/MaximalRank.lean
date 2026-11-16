module

public import NSP14.Green.Perturbation
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [Infinite k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- Tangent-space property of a maximum-rank pencil, proved by an actual
nonvanishing minor along a line, in every characteristic. -/
theorem maximal_rank_kernel (F G : V →ₗ[k] W)
    (hmax : ∀ t : k, Module.finrank k (F + t • G).range ≤ Module.finrank k F.range)
    (y : V) (hy : F y = 0) : G y ∈ F.range := by
  by_contra hnot
  let B := Module.finBasis k F.range
  let u : Fin (Module.finrank k F.range) → V := fun i => (B i).property.choose
  have hu (i : Fin (Module.finrank k F.range)) : F (u i) = (B i).val :=
    (B i).property.choose_spec
  have hb : LinearIndependent k (fun i => (B i).val) :=
    B.linearIndependent.map' F.range.subtype (Submodule.ker_subtype _)
  have hs : Submodule.span k (Set.range (fun i => (B i).val)) ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact (B i).property
  have hind : LinearIndependent k
      (fun o : Option (Fin (Module.finrank k F.range)) => Option.casesOn' o (G y) (fun i => F (u i))) := by
    simpa only [hu] using hb.option (fun h => hnot (hs h))
  obtain ⟨t, ht, hlin⟩ := generic_independent_line
    (fun o : Option (Fin (Module.finrank k F.range)) => Option.casesOn' o (G y) (fun i => F (u i)))
    (fun o : Option (Fin (Module.finrank k F.range)) => Option.casesOn' o 0 (fun i => G (u i))) hind
  let family : Option (Fin (Module.finrank k F.range)) → W :=
    fun o => Option.casesOn' o (G y) (fun i => F (u i)) +
      t • Option.casesOn' o 0 (fun i => G (u i))
  have hmem (o : Option (Fin (Module.finrank k F.range))) : family o ∈ (F + t • G).range := by
    cases o with
    | none =>
      refine ⟨t⁻¹ • y, ?_⟩
      simp [family, hy, LinearMap.add_apply, LinearMap.smul_apply, smul_smul, ht]
    | some i =>
      exact ⟨u i, rfl⟩
  have hLI : LinearIndependent k (fun o => (⟨family o, hmem o⟩ : (F + t • G).range)) :=
    LinearIndependent.of_comp (F + t • G).range.subtype hlin
  have hc := hLI.fintype_card_le_finrank
  simp only [Fintype.card_option, Fintype.card_fin] at hc
  have hm := hmax t
  omega

end NSP14.Green
