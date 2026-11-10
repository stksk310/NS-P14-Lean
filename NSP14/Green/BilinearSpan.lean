module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace NSP14.Green

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def bilinearSpan (μ : V →ₗ[k] V →ₗ[k] W) : Submodule k W :=
  Submodule.span k {w | ∃ x y, μ x y = w}

noncomputable def symmetricBasisProduct {ι : Type*} (B : Module.Basis ι k V)
    (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x) : Sym2 ι → W :=
  Sym2.lift ⟨fun i j => μ (B i) (B j), fun i j => hs (B i) (B j)⟩

@[simp] theorem symmetricBasisProduct_pair {ι : Type*} (B : Module.Basis ι k V)
    (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x) (i j : ι) :
    symmetricBasisProduct B μ hs s(i,j) = μ (B i) (B j) := rfl

/-- Products of actual basis vectors span every bilinear product. -/
theorem basis_product_span {ι : Type*} [Fintype ι] (B : Module.Basis ι k V)
    (μ : V →ₗ[k] V →ₗ[k] W) (hs : ∀ x y, μ x y = μ y x) :
    bilinearSpan μ ≤ Submodule.span k (Set.range (symmetricBasisProduct B μ hs)) := by
  apply Submodule.span_le.mpr
  rintro z ⟨x,y,rfl⟩
  rw [← B.sum_repr x, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_smul]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [← B.sum_repr y, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨s(i,j), rfl⟩

/-- Arbitrary-characteristic symmetric-square dimension bound, by actual spanning products. -/
theorem symmetric_span_bound [Module.Finite k V] (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤) :
    Module.finrank k W ≤ (Module.finrank k V + 1).choose 2 := by
  let B := Module.finBasis k V
  have hb : Submodule.span k (Set.range (symmetricBasisProduct B μ hs)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact basis_product_span B μ hs
  have hc := finrank_le_of_span_eq_top hb
  simpa only [Sym2.card, Fintype.card_fin] using hc

/-- Alternating products need only off-diagonal pairs; no division by two occurs. -/
theorem alternating_span_bound [Module.Finite k V] (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (ha : ∀ x, μ x x = 0)
    (hspan : bilinearSpan μ = ⊤) :
    Module.finrank k W ≤ (Module.finrank k V).choose 2 := by
  let B := Module.finBasis k V
  let f : {p : Sym2 (Fin (Module.finrank k V)) // ¬p.IsDiag} → W :=
    fun p => symmetricBasisProduct B μ hs p.val
  have hle : Submodule.span k (Set.range (symmetricBasisProduct B μ hs)) ≤
      Submodule.span k (Set.range f) := by
    apply Submodule.span_le.mpr
    rintro z ⟨p,rfl⟩
    by_cases hd : p.IsDiag
    · rw [← Sym2.diag_diagElem hd]
      change μ (B (p.diagElem hd)) (B (p.diagElem hd)) ∈ _
      rw [ha]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨p,hd⟩,rfl⟩
  have hb : Submodule.span k (Set.range f) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact (basis_product_span B μ hs).trans hle
  have hc := finrank_le_of_span_eq_top hb
  simpa only [Sym2.card_subtype_not_diag, Fintype.card_fin] using hc

end NSP14.Green
