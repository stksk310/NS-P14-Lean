module

public import NSP14.Semigroup.TowerIdeals

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Finite actual head degrees, after proving the head basis finite. -/
noncomputable def headTopDegree : ℕ :=
  Finset.univ.sup (fun h : S.HeadExponent => S.order h.val.val)

theorem head_order_le_top (h : S.HeadExponent) : S.order h.val.val ≤ S.headTopDegree :=
  Finset.le_sup (f := fun h : S.HeadExponent => S.order h.val.val) (Finset.mem_univ h)

variable (k : Type*) [Field k]

theorem headDegree_eq_bot_of_headTop_lt (n : ℕ) (hn : S.headTopDegree < n) :
    S.headDegree k n = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply (S.headQuotientEquiv k).injective
  ext h
  have hne : S.order h.val.val ≠ n := by have := S.head_order_le_top h; omega
  exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n a).1 ha) h hne

theorem towerStageDegree_eq_bot_of_headTop_lt (s n : ℕ) (hn : S.headTopDegree < n) :
    S.towerStageDegree k s n = ⊥ := by
  unfold towerStageDegree
  rw [S.headDegree_eq_bot_of_headTop_lt k n hn, Submodule.map_bot]

/-- One actual tower-derived sequence. Its definition makes no cut choice and
is later to be restricted to the single P selected by Green. -/
noncomputable def towerResource (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 2 S.qTopDegree, Module.finrank k (S.towerStageDegree k s (s + t))

theorem towerResource_zero : S.towerResource k 0 = S.deficit := by
  unfold towerResource
  simp only [Nat.add_zero]
  have he : ∀ s ∈ Finset.Icc 2 S.qTopDegree,
      Module.finrank k (S.towerStageDegree k s s) = Module.finrank k (S.qDegree k s) :=
    fun s _ => (S.towerStageLowDegreeEquiv k s s le_rfl).finrank_eq
  rw [Finset.sum_congr rfl he]
  have hsum := S.qDegree_high_sum k
  have hsub : Finset.Icc 2 S.qTopDegree ⊆ Finset.Icc 2 (S.deficit + 1) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
      (Finset.mem_Icc.mp hs).2.trans S.qTopDegree_le_deficit⟩
  rw [← hsum]
  apply Finset.sum_subset hsub
  intro s hs hn
  have ht : S.qTopDegree < s := by
    have hs2 := (Finset.mem_Icc.mp hs).1
    by_contra hh
    exact hn (Finset.mem_Icc.mpr ⟨hs2, by omega⟩)
  rw [S.qDegree_eq_bot_of_top_lt k s ht]
  simp

theorem towerResource_vanish (t : ℕ) (ht : S.headTopDegree < t) :
    S.towerResource k t = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [S.towerStageDegree_eq_bot_of_headTop_lt k s (s + t) (by omega)]
  simp

/-- All tail degrees are retained; this support is not a scalar cutoff. -/
noncomputable def towerResourceSupport : Finset ℕ := Finset.range (S.headTopDegree + 1)

theorem towerResource_outside_support (t : ℕ) (ht : t ∉ S.towerResourceSupport) :
    S.towerResource k t = 0 := by
  apply S.towerResource_vanish k
  change t ∉ Finset.range (S.headTopDegree + 1) at ht
  simp only [Finset.mem_range, not_lt] at ht
  omega

theorem towerResource_eq_zero_of_deficit_zero (h : S.deficit = 0) (t : ℕ) :
    S.towerResource k t = 0 := by
  unfold towerResource
  have ht := S.qTopDegree_le_deficit
  rw [h] at ht
  have he : Finset.Icc 2 S.qTopDegree = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
  rw [he, Finset.sum_empty]

end NSP14.NumericalSemigroup
