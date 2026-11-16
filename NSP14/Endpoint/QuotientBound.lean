module
public import NSP14.Homological.FiniteKoszulEuler
public import NSP14.Homological.ZerothBettiEpi
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint
universe u
variable (k : Type u) [Field k]

/-- The actual LES bound for a quotient, retaining the preceding
kernel homology degree. -/
theorem homology_quotient_bound
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite k (S.X₂.homology (i+1))] [Module.Finite k (S.X₃.homology (i+1))]
    [Module.Finite k (S.X₁.homology i)] :
    Module.finrank k (S.X₃.homology (i+1))≤Module.finrank k (S.X₂.homology (i+1))+
      Module.finrank k (S.X₁.homology i) := by
  have he := exact_rank_sum k _ (hS.homology_exact₃ (i+1) i rfl)
  have hleft := LinearMap.finrank_range_le (homologyMap S.g (i+1)).hom
  have hright := Submodule.finrank_le (hS.δ (i+1) i rfl).hom.range
  dsimp only at he
  omega

variable (σ : Type u) [Fintype σ]
  (S : ShortComplex (ModuleCat.{u} (VariableRing k σ))) (hS : S.ShortExact)
  [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃]

include hS in
theorem quotient_betti_bound (i : ℕ) :
    totalBetti k σ S.X₃ (i+1)≤totalBetti k σ S.X₂ (i+1)+totalBetti k σ S.X₁ i := by
  have h := homology_quotient_bound k (coefficientKoszulSequence k σ S)
    (coefficientKoszulSequence_shortExact k σ S hS) i
  change Module.finrank k ((coefficientKoszulComplex k σ S.X₃).homology (i+1))≤
    Module.finrank k ((coefficientKoszulComplex k σ S.X₂).homology (i+1))+
      Module.finrank k ((coefficientKoszulComplex k σ S.X₁).homology i) at h
  rw [(coefficientKoszulHomologyIso k σ S.X₃ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₂ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₁ i).toLinearEquiv.finrank_eq] at h
  exact h

omit S hS [Module.Finite (VariableRing k σ) S.X₁]
    [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃] in
theorem finite_betti_bound (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)] (i : ℕ) :
    totalBetti k σ M i≤Module.finrank k (coefficientModule k σ M)*(Fintype.card σ).choose i := by
  have h := koszul_betti_chain_rank k σ M i
  omega
end NSP14.Endpoint
