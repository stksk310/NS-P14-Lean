module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable {I A V : Type*} [Fintype I] [Fintype A] [Fintype V] [Nonempty V]
  (a : I → A) (E : I → V → Prop)

noncomputable def pivotCount (α : A) (v : V) : ℕ :=
  ∑ i : I,if a i=α ∧ E i v then 1 else 0

noncomputable def maximizingPivot (α : A) : V :=
  (Finset.exists_max_image Finset.univ (pivotCount a E α) Finset.univ_nonempty).choose

omit [Fintype A] in
theorem maximizingPivot_max (α : A) (v : V) :
    pivotCount a E α v ≤ pivotCount a E α (maximizingPivot a E α) :=
  (Finset.exists_max_image Finset.univ (pivotCount a E α) Finset.univ_nonempty).choose_spec.2 v (Finset.mem_univ v)

/-- Averaging is performed in Q, entirely outside the coefficient field.
The maximizing choice is constant on each augmented-term fiber. -/
theorem weighted_pivot_bound (w : A → V → ℚ)
    (hw : ∀ α v,0 ≤ w α v) (hs : ∀ α,∑ v,w α v=1) :
    (∑ i : I,∑ v : V,if E i v then w (a i) v else 0) ≤
      (Nat.card {i : I // E i (maximizingPivot a E (a i))} : ℚ) := by
  classical
  have hf (α : A) :
      (∑ i ∈ Finset.univ.filter (fun i => a i=α),∑ v : V,if E i v then w (a i) v else 0) ≤
      ∑ i ∈ Finset.univ.filter (fun i => a i=α),if E i (maximizingPivot a E (a i)) then (1:ℚ) else 0 := by
    have hc (v : V) :
        (∑ i ∈ Finset.univ.filter (fun i => a i=α),if E i v then w (a i) v else 0)=
          w α v*(pivotCount a E α v : ℚ) := by
      rw [pivotCount,Nat.cast_sum,Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i=α <;> by_cases he : E i v <;> simp [hi,he]
    have hc' :
        (∑ i ∈ Finset.univ.filter (fun i => a i=α),if E i (maximizingPivot a E (a i)) then (1:ℚ) else 0)=
          (pivotCount a E α (maximizingPivot a E α) : ℚ) := by
      simp only [pivotCount,Nat.cast_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i=α <;> simp [hi]
    rw [Finset.sum_comm]
    simp_rw [hc]
    rw [hc']
    calc
      _ ≤ ∑ v : V,w α v*(pivotCount a E α (maximizingPivot a E α) : ℚ) := by
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (maximizingPivot_max a E α v)) (hw α v)
      _ = _ := by rw [← Finset.sum_mul,hs,one_mul]
  have hall := Finset.sum_le_sum (s:=Finset.univ) (fun α _ => hf α)
  rw [Finset.sum_fiberwise (Finset.univ : Finset I) a
    (fun i => ∑ v : V,if E i v then w (a i) v else 0),
    Finset.sum_fiberwise (Finset.univ : Finset I) a
    (fun i => if E i (maximizingPivot a E (a i)) then (1:ℚ) else 0)] at hall
  convert hall using 1
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,Nat.cast_sum]
  simp
end NSP14.Homological
