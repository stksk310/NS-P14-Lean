module

public import NSP14.Homological.KoszulExactness
public import Mathlib.RingTheory.Finiteness.Finsupp

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- Finite-dimensional endpoints suffice; the middle space is not assumed finite. -/
theorem exact_finite_of_ends (S : ShortComplex (ModuleCat.{u} k)) (hS : S.Exact)
    [Module.Finite k S.X₁] [Module.Finite k S.X₃] : Module.Finite k S.X₂ := by
  have he : Function.Exact S.f.hom S.g.hom.rangeRestrict := by
    intro x
    change (S.g.hom.rangeRestrict x=0 ↔ ∃ y,S.f.hom y=x)
    rw [Subtype.ext_iff]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS x
  exact Module.Finite.of_exact he S.g.hom.surjective_rangeRestrict

theorem homology_finite_of_ends
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₁.homology i)] [Module.Finite k (S.X₃.homology i)] :
    Module.Finite k (S.X₂.homology i) :=
  exact_finite_of_ends k _ (hS.homology_exact₂ i)

/-- Homology can shrink along a filtration; no degeneration assertion is used. -/
theorem homology_finrank_bound
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₁.homology i)] [Module.Finite k (S.X₃.homology i)] :
    Module.finrank k (S.X₂.homology i) ≤
      Module.finrank k (S.X₁.homology i) + Module.finrank k (S.X₃.homology i) := by
  let : Module.Finite k (S.X₂.homology i) := homology_finite_of_ends k S hS i
  have he := exact_rank_sum k _ (hS.homology_exact₂ i)
  dsimp only at he
  have hf := (homologyMap S.f i).hom.finrank_range_le
  have hg := Submodule.finrank_le (homologyMap S.g i).hom.range
  omega

/-- Quotients of actual monic chain maps, not prescribed numerical Betti arrays. -/
noncomputable def filteredQuotient
    {A B : ChainComplex (ModuleCat.{u} k) ℕ} (f : A ⟶ B) := cokernel f

theorem filteredShortExact {A B : ChainComplex (ModuleCat.{u} k) ℕ} (f : A ⟶ B) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

/-- A finite filtration by actual chain subobjects bounds the final homology by the sum
of the quotient homologies. Quotient finiteness supplies all intermediate finiteness. -/
theorem boundedFilteredComparison
    (C : ℕ → ChainComplex (ModuleCat.{u} k) ℕ) (f : ∀ j,C j ⟶ C (j+1))
    [∀ j,Mono (f j)] (i : ℕ) (hzero : IsZero ((C 0).homology i))
    (hfinite : ∀ j,Module.Finite k ((filteredQuotient k (f j)).homology i)) (n : ℕ) :
    Module.Finite k ((C n).homology i) ∧
      Module.finrank k ((C n).homology i) ≤
        ∑ j∈Finset.range n,Module.finrank k ((filteredQuotient k (f j)).homology i) := by
  induction n with
  | zero =>
    have : Subsingleton ((C 0).homology i) := ModuleCat.subsingleton_of_isZero hzero
    exact ⟨inferInstance,by simp [Module.finrank_zero_of_subsingleton]⟩
  | succ n ih =>
    let : Module.Finite k ((C n).homology i) := ih.1
    let : Module.Finite k ((cokernel (f n)).homology i) := hfinite n
    have hs := filteredShortExact k (f n)
    have hf := homology_finite_of_ends k _ hs i
    refine ⟨hf,?_⟩
    have hb := homology_finrank_bound k _ hs i
    change Module.finrank k ((C (n+1)).homology i) ≤ _
    rw [Finset.sum_range_succ]
    exact hb.trans (Nat.add_le_add_right ih.2 _)

end NSP14.Homological
