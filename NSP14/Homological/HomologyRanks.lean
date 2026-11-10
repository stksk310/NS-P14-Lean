module

public import NSP14.Homological.Betti
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- Exactness gives rank Euler without natural-number subtraction. Only the middle space is finite. -/
theorem exact_rank_sum (S : ShortComplex (ModuleCat.{u} k)) (hS : S.Exact)
    [Module.Finite k S.X₂] :
    Module.finrank k S.f.hom.range + Module.finrank k S.g.hom.range=Module.finrank k S.X₂ := by
  have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mp hS
  rw [he,add_comm]
  exact S.g.hom.finrank_range_add_finrank_ker

/-- The two correction ranks retain their adjacent homological indices.
The hypothesis is short exactness of actual complexes, not a dimension-only replacement. -/
theorem homology_rank_correction
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₁.homology (i+1))]
    [Module.Finite k (S.X₂.homology (i+1))]
    [Module.Finite k (S.X₃.homology (i+1))] :
    Module.finrank k (S.X₂.homology (i+1)) +
      Module.finrank k (hS.δ (i+1) i rfl).hom.range +
      Module.finrank k (hS.δ (i+2) (i+1) rfl).hom.range =
    Module.finrank k (S.X₁.homology (i+1)) + Module.finrank k (S.X₃.homology (i+1)) := by
  have h1 := exact_rank_sum k _ (hS.homology_exact₁ (i+2) (i+1) rfl)
  have h2 := exact_rank_sum k _ (hS.homology_exact₂ (i+1))
  have h3 := exact_rank_sum k _ (hS.homology_exact₃ (i+1) i rfl)
  dsimp only at h1 h2 h3
  omega

theorem homology_finrank_le
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₁.homology (i+1))]
    [Module.Finite k (S.X₂.homology (i+1))]
    [Module.Finite k (S.X₃.homology (i+1))] :
    Module.finrank k (S.X₂.homology (i+1)) ≤
      Module.finrank k (S.X₁.homology (i+1)) + Module.finrank k (S.X₃.homology (i+1)) := by
  have h := homology_rank_correction k S hS i
  omega

/-- Degree zero has only the incoming correction; there is no hidden negative homological degree. -/
theorem homology_rank_correction_zero
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact)
    [Module.Finite k (S.X₁.homology 0)]
    [Module.Finite k (S.X₂.homology 0)]
    [Module.Finite k (S.X₃.homology 0)] :
    Module.finrank k (S.X₂.homology 0) + Module.finrank k (hS.δ 1 0 rfl).hom.range =
      Module.finrank k (S.X₁.homology 0) + Module.finrank k (S.X₃.homology 0) := by
  have hi := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS 0
  let : Epi (S.g.f 0) := hi.epi_g
  let : Epi (homologyMap S.g 0) := epi_homologyMap_of_epi_of_not_rel S.g 0 (by
    intro j h; change j+1=0 at h; omega)
  have he : (homologyMap S.g 0).hom.range=⊤ := LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have h1 := exact_rank_sum k _ (hS.homology_exact₁ 1 0 rfl)
  have h2 := exact_rank_sum k _ (hS.homology_exact₂ 0)
  dsimp only at h1 h2
  rw [he,finrank_top] at h2
  omega

end NSP14.Homological
