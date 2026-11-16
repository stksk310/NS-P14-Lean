module
public import NSP14.Homological.VandermondeSpark
public import NSP14.Homological.LinearVariableBetti
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] (r : ℕ)
  (index : σ ≃ Fin r) (points : σ → k)

noncomputable def evaluationVariableMap : (σ → k) →ₗ[k] (σ → k) :=
  Fintype.linearCombination k (fun j i => points j^(index i).val)

include index in
theorem evaluationVariableMap_injective (hp : Function.Injective points) :
    Function.Injective (evaluationVariableMap k σ r index points) := by
  have hc : Fintype.card σ ≤ r := by
    have h := Fintype.card_congr index
    simpa using h.le
  have hi := momentVectors_independent k points hp hc
  have hLI : LinearIndependent k (fun j i => points j^(index i).val) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hz j
    apply (Fintype.linearIndependent_iff.mp hi) c ?_ j
    funext i
    obtain ⟨s,hs⟩ := index.surjective i
    have he := congrFun hz s
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,hs] at he ⊢
    exact he
  exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hLI

noncomputable def evaluationVariableEquiv (hp : Function.Injective points) : (σ → k) ≃ₗ[k] (σ → k) :=
  LinearEquiv.ofInjectiveEndo (evaluationVariableMap k σ r index points)
    (evaluationVariableMap_injective k σ r index points hp)

theorem evaluationVariableEquiv_single (hp : Function.Injective points) (j i : σ) :
    evaluationVariableEquiv k σ r index points hp (Pi.single j 1) i=points j^(index i).val := by
  change evaluationVariableMap k σ r index points (Pi.single j 1) i=_
  rw [evaluationVariableMap,Fintype.linearCombination_apply_single]
  simp only [one_smul]
end NSP14.Homological
