module
public import NSP14.Homological.KoszulRanks
public import NSP14.Homological.CoefficientKoszulFunctor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k]

theorem homology_quotient_additivity
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₂.homology (i+1))]
    [Module.Finite k (S.X₃.homology (i+1))] [Module.Finite k (S.X₁.homology i)]
    (hfi : homologyMap S.f (i+1)=0) (hf0 : homologyMap S.f i=0) :
    Module.finrank k (S.X₃.homology (i+1))=
      Module.finrank k (S.X₂.homology (i+1))+Module.finrank k (S.X₁.homology i) := by
  have h1 := exact_rank_sum k _ (hS.homology_exact₂ (i+1))
  have h2 := exact_rank_sum k _ (hS.homology_exact₃ (i+1) i rfl)
  have h3 := exact_rank_sum k _ (hS.homology_exact₁ (i+1) i rfl)
  dsimp only at h1 h2 h3
  have hz1 : Module.finrank k (homologyMap S.f (i+1)).hom.range=0 := by
    rw [hfi,ModuleCat.hom_zero,LinearMap.range_zero,finrank_bot]
  have hz0 : Module.finrank k (homologyMap S.f i).hom.range=0 := by
    rw [hf0,ModuleCat.hom_zero,LinearMap.range_zero,finrank_bot]
  omega

variable (σ : Type u) [Fintype σ]
  (S : ShortComplex (ModuleCat.{u} (VariableRing k σ))) (hS : S.ShortExact)
  [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃]

include hS in
/-- The usual quotient Betti additivity is proved from the real LES,
when the actual left module map is zero on the actual homology. -/
theorem koszul_quotient_betti_additivity (i : ℕ)
    (hf : ∀ j,homologyMap ((coefficientKoszulFunctor k σ).map S.f) j=0) :
    totalBetti k σ S.X₃ (i+1)=totalBetti k σ S.X₂ (i+1)+totalBetti k σ S.X₁ i := by
  have h := homology_quotient_additivity k (coefficientKoszulSequence k σ S)
    (coefficientKoszulSequence_shortExact k σ S hS) i (hf (i+1)) (hf i)
  change Module.finrank k ((coefficientKoszulComplex k σ S.X₃).homology (i+1))=
    Module.finrank k ((coefficientKoszulComplex k σ S.X₂).homology (i+1))+
      Module.finrank k ((coefficientKoszulComplex k σ S.X₁).homology i) at h
  rw [(coefficientKoszulHomologyIso k σ S.X₃ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₂ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₁ i).toLinearEquiv.finrank_eq] at h
  exact h
end NSP14.Homological
