module
public import NSP14.Homological.GradedMonomials
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
  (G : GradedPolynomialModule k σ M) [Module.Finite k (coefficientModule k σ M)]

noncomputable instance gradedPieceFinite (b : ℤ) : Module.Finite k (G.piece b) :=
  Module.Finite.of_injective (G.inclusion b) (G.inclusion_injective k σ b)

noncomputable def degreeGenerators (b : ℤ) :
    Fin (Module.finrank k (G.piece b)) → coefficientModule k σ M :=
  fun i => G.inclusion b (Module.finBasis k (G.piece b) i)

theorem degreeGenerators_homogeneous (b : ℤ) (i : Fin (Module.finrank k (G.piece b))) :
    degreeGenerators k σ M G b i ∈ G.degreeSpace b :=
  ⟨Module.finBasis k (G.piece b) i,rfl⟩

theorem degreeGenerators_coefficient_span (b : ℤ) :
    Submodule.span k (Set.range (degreeGenerators k σ M G b))=G.degreeSpace b := by
  have he : Set.range (degreeGenerators k σ M G b)=
      (G.inclusion b) '' Set.range (Module.finBasis k (G.piece b)) := by
    ext a
    simp only [degreeGenerators,Set.mem_range,Set.mem_image]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [he,← Submodule.map_span,(Module.finBasis k (G.piece b)).span_eq,
    Submodule.map_top]
  rfl

theorem degreeGenerators_polynomial_span (b : ℤ)
    (hgen : Submodule.span (VariableRing k σ)
      (Set.range (fun a : G.piece b => (show M from G.inclusion b a)))=⊤) :
    Submodule.span (VariableRing k σ) (Set.range (degreeGenerators k σ M G b))=⊤ := by
  let U := Submodule.span (VariableRing k σ) (Set.range (degreeGenerators k σ M G b))
  have hle : G.degreeSpace b ≤ U.restrictScalars k := by
    rw [← degreeGenerators_coefficient_span k σ M G b]
    exact Submodule.span_le.mpr (fun a ha => Submodule.subset_span ha)
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro a ⟨a,rfl⟩
  exact hle ⟨a,rfl⟩
end NSP14.Homological
