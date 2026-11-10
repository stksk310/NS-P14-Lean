module

public import NSP14.Green.BilinearQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The actual quadratic image of a subspace of linear forms. -/
def cutImage (μ : V →ₗ[k] V →ₗ[k] W) (E : Submodule k V) : Submodule k W :=
  Submodule.span k {w | ∃ x ∈ E, ∃ y, μ x y = w}

theorem product_mem_cutImage (μ : V →ₗ[k] V →ₗ[k] W) (E : Submodule k V)
    (x : V) (hx : x ∈ E) (y : V) : μ x y ∈ cutImage μ E :=
  Submodule.subset_span ⟨x,hx,y,rfl⟩

theorem cutImage_mono (μ : V →ₗ[k] V →ₗ[k] W) : Monotone (cutImage μ) := by
  intro E F h
  apply Submodule.span_mono
  rintro w ⟨x,hx,y,rfl⟩
  exact ⟨x,h hx,y,rfl⟩

@[simp] theorem cutImage_bot (μ : V →ₗ[k] V →ₗ[k] W) : cutImage μ ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro w ⟨x,hx,y,rfl⟩
  have hx0 : x = 0 := hx
  simp [hx0]

theorem cutImage_sup (μ : V →ₗ[k] V →ₗ[k] W) (E F : Submodule k V) :
    cutImage μ (E ⊔ F) = cutImage μ E ⊔ cutImage μ F := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨x,hx,y,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _
      ((show cutImage μ E ≤ cutImage μ E ⊔ cutImage μ F from le_sup_left)
        (product_mem_cutImage μ E a ha y))
      ((show cutImage μ F ≤ cutImage μ E ⊔ cutImage μ F from le_sup_right)
        (product_mem_cutImage μ F b hb y))
  · exact sup_le (cutImage_mono μ le_sup_left) (cutImage_mono μ le_sup_right)

theorem cutImage_singleton (μ : V →ₗ[k] V →ₗ[k] W) (x : V) :
    cutImage μ (Submodule.span k {x}) = (μ x).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨z,hz,y,rfl⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, LinearMap.smul_apply]
    exact (μ x).range.smul_mem c ⟨y,rfl⟩
  · rintro w ⟨y,rfl⟩
    exact product_mem_cutImage μ _ x (Submodule.subset_span (Set.mem_singleton x)) y

theorem cutImage_sup_singleton (μ : V →ₗ[k] V →ₗ[k] W) (E : Submodule k V) (x : V) :
    cutImage μ (E ⊔ Submodule.span k {x}) = cutImage μ E ⊔ (μ x).range := by
  rw [cutImage_sup, cutImage_singleton]

noncomputable def cutProduct (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) : (V ⧸ E) →ₗ[k] (V ⧸ E) →ₗ[k] (W ⧸ cutImage μ E) :=
  quotientBilinear μ E (cutImage μ E) (product_mem_cutImage μ E) hs

@[simp] theorem cutProduct_mk (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) (x y : V) :
    cutProduct μ hs E (E.mkQ x) (E.mkQ y) = (cutImage μ E).mkQ (μ x y) := rfl

theorem cutProduct_symmetric (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) : ∀ x y, cutProduct μ hs E x y = cutProduct μ hs E y x :=
  quotientBilinear_symmetric μ _ _ _ hs

theorem cutProduct_spans (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) (hspan : bilinearSpan μ = ⊤) : bilinearSpan (cutProduct μ hs E) = ⊤ :=
  quotientBilinear_spans μ _ _ _ hs hspan

theorem cutProduct_range (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) (x : V) :
    (cutProduct μ hs E (E.mkQ x)).range = (μ x).range.map (cutImage μ E).mkQ := by
  apply le_antisymm
  · rintro w ⟨y,rfl⟩
    refine Submodule.Quotient.induction_on E y ?_
    intro z
    exact ⟨μ x z, ⟨z,rfl⟩, rfl⟩
  · rintro w ⟨z,⟨y,rfl⟩,rfl⟩
    exact ⟨E.mkQ y,rfl⟩

/-- The next quadratic quotient is the quotient for the enlarged same cut,
with the actual third-isomorphism map. -/
noncomputable def cutStepEquiv (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x)
    (E : Submodule k V) (x : V) :
    ((W ⧸ cutImage μ E) ⧸ (cutProduct μ hs E (E.mkQ x)).range) ≃ₗ[k]
      (W ⧸ cutImage μ (E ⊔ Submodule.span k {x})) :=
  (Submodule.quotEquivOfEq _ _ (cutProduct_range μ hs E x)).trans
    ((Submodule.quotientQuotientEquivQuotientSup (cutImage μ E) (μ x).range).trans
      (Submodule.quotEquivOfEq _ _ (cutImage_sup_singleton μ E x).symm))

end NSP14.Green
