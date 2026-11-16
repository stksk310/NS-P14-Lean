module

public import NSP14.Green.FlagSpan
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open scoped Classical

namespace NSP14.Green

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Independent forms can be padded inside the original degree-one space. -/
theorem extend_independent {n m : ℕ} (c : Fin n → V) (hc : LinearIndependent k c)
    (hnm : n ≤ m) (hm : m ≤ Module.finrank k V) :
    ∃ d : Fin m → V, LinearIndependent k d ∧
      Submodule.span k (Set.range c) ≤ Submodule.span k (Set.range d) := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨c,hc,le_rfl⟩
  | @succ m hnm ih =>
    obtain ⟨d,hd,hs⟩ := ih (by omega)
    have hr : Module.finrank k (Submodule.span k (Set.range d)) = m := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hd
    obtain ⟨x,hx⟩ : ∃ x : V, x ∉ Submodule.span k (Set.range d) := by
      by_contra hn
      push Not at hn
      have ht : Submodule.span k (Set.range d) = ⊤ := by
        apply top_unique
        intro x _
        exact hn x
      have he := congrArg (fun U : Submodule k V => Module.finrank k U) ht
      rw [hr, finrank_top] at he
      omega
    refine ⟨Fin.snoc d x, hd.finSnoc hx, hs.trans ?_⟩
    have he := flagSpan_snoc_full (k := k) d x
    rw [flagSpan_full,flagSpan_full] at he
    rw [he]
    exact le_sup_left

end NSP14.Green
