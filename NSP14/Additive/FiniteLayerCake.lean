module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.NormNum
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
theorem sum_range_indicator_lt (u d : ℕ) (hd : d ≤ u) :
    ∑ n ∈ Finset.range u, (if n < d then 1 else 0) = d := by
  rw [←Finset.card_filter]
  have he : (Finset.range u).filter (fun n => n < d) = Finset.range d := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he,Finset.card_range]

/-- A finite layer cake. No infinite sum or finite-support assumption is used. -/
theorem finite_layer_cake {ι : Type*} [Fintype ι] (f : ι → ℕ) (u : ℕ)
    (hf : ∀ i, f i ≤ u) :
    ∑ i, f i = ∑ n ∈ Finset.range u, (Finset.univ.filter (fun i => n < f i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (sum_range_indicator_lt u (f i) (hf i)).symm
end NSP14.Additive
