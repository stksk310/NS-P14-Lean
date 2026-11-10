module

public import NSP14.Semigroup.JumpHomogeneity
public import NSP14.Semigroup.ActualFinite
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- F_s is an actual homogeneous ideal of A, not an arbitrary numerical profile. -/
noncomputable def jumpIdeal (s : ℕ) : Ideal (S.HeadAlgebra k) where
  carrier := S.jumpASpace k s
  zero_mem' := (S.jumpASpace k s).zero_mem
  add_mem' := (S.jumpASpace k s).add_mem
  smul_mem' r a ha := S.jumpASpace_mul k s r a ha

@[simp] theorem jumpIdeal_restrictScalars (s : ℕ) :
    (S.jumpIdeal k s).restrictScalars k = S.jumpASpace k s := rfl

theorem jumpIdeal_homogeneous (s p : ℕ) (a : S.HeadAlgebra k)
    (ha : a ∈ S.jumpIdeal k s) : S.headGradeProject k p a ∈ S.jumpIdeal k s :=
  S.headGradeProject_mem_jumpASpace k s p a ha

theorem jumpIdeal_le_nonAperyIdeal (s : ℕ) : S.jumpIdeal k s ≤ S.nonAperyIdeal k := by
  intro a ha
  apply (S.mem_nonAperySpace k a).2
  intro h hh
  have hac : S.headQuotientEquiv k a ∈ Finsupp.supported k k
      {t : S.HeadExponent | t.val.val ∉ S.aperySet ∧
        S.jump (t.val.val - S.multiplicity) ≤ s} := ha
  exact (Finsupp.mem_supported' k _).1 hac h (fun ht => ht.1 hh)

theorem jumpIdeal_monotone : Monotone (S.jumpIdeal k) := by
  intro s t hst a ha
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k
    {h : S.HeadExponent | h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s} at ha
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k
    {h : S.HeadExponent | h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ t}
  rw [Finsupp.mem_supported'] at ha ⊢
  intro h hh
  exact ha h (fun hs => hh ⟨hs.1, hs.2.trans hst⟩)

theorem jumpIdeal_one : S.jumpIdeal k 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hN := S.jumpIdeal_le_nonAperyIdeal k 1 ha
  have hasc : (⟨a,hN⟩ : (S.nonAperyIdeal k).restrictScalars k) ∈ S.ascendingJump k 1 := ha
  rw [S.ascendingJump_one] at hasc
  exact congrArg Subtype.val hasc

theorem jumpIdeal_top : S.jumpIdeal k S.qTopDegree = S.nonAperyIdeal k := by
  apply le_antisymm (S.jumpIdeal_le_nonAperyIdeal k _)
  intro a ha
  have hasc : (⟨a,ha⟩ : (S.nonAperyIdeal k).restrictScalars k) ∈
      S.ascendingJump k S.qTopDegree := by rw [S.ascendingJump_top]; trivial
  exact hasc

/-- Low-degree non-Apéry vectors have already entered F_{s-1}. This is the
actual-coordinate assertion behind U_s agreeing with Q through degree s. -/
theorem lowDegree_nonApery_mem_jumpIdeal (s n : ℕ) (hn : n ≤ s)
    (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k n) (hN : a ∈ S.nonAperyIdeal k) :
    a ∈ S.jumpIdeal k (s - 1) := by
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro h hh
  by_cases hap : h.val.val ∈ S.aperySet
  · exact (S.mem_nonAperySpace k a).1 hN h hap
  have hterm := S.head_sub_terminal (⟨h.property, hap⟩ : S.NonAperyHead h.val.val)
  have hj : s - 1 < S.jump (h.val.val - S.multiplicity) := by
    by_contra hle
    exact hh ⟨hap, by omega⟩
  have hp := S.order_pos hterm.1 (S.terminal_pos hterm)
  obtain ⟨x, hx, he⟩ := S.head_predecessor (⟨h.property, hap⟩ : S.NonAperyHead h.val.val)
  have ho := S.order_add_multiplicity hterm.1
  have hhead : S.order h.val.val = S.order (h.val.val - S.multiplicity) +
      S.jump (h.val.val - S.multiplicity) := by
    unfold jump
    have he' : h.val.val - S.multiplicity + S.multiplicity = h.val.val := by omega
    rw [he'] at ho ⊢
    omega
  have hne : S.order h.val.val ≠ n := by omega
  exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n a).1 ha) h hne

/-- The actual stage U_s=A/F_{s-1}. Its quotient action comes from S₀. -/
abbrev TowerStage (s : ℕ) := S.HeadAlgebra k ⧸ S.jumpIdeal k (s - 1)

noncomputable def towerStageToQ (s : ℕ) : S.TowerStage k s →ₐ[k] S.AperyAlgebra k :=
  Ideal.Quotient.factorₐ k (S.jumpIdeal_le_nonAperyIdeal k (s - 1))

noncomputable def towerStageDegree (s n : ℕ) : Submodule k (S.TowerStage k s) :=
  (S.headDegree k n).map (Ideal.Quotient.mkₐ k (S.jumpIdeal k (s - 1))).toLinearMap

noncomputable def towerStageToQDegree (s n : ℕ) :
    S.towerStageDegree k s n →ₗ[k] S.qDegree k n where
  toFun a := ⟨S.towerStageToQ k s a.val, by
    obtain ⟨b, hb, he⟩ := a.property
    rw [← he]
    exact S.headDegree_to_qDegree k n b hb⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext ((S.towerStageToQ k s).toLinearMap.map_smul r a.val)

theorem towerStageToQDegree_surjective (s n : ℕ) :
    Function.Surjective (S.towerStageToQDegree k s n) := by
  intro a
  obtain ⟨b, hb⟩ := S.headToQDegree_surjective k n a
  refine ⟨⟨Ideal.Quotient.mk _ b.val, b.val, b.property, rfl⟩, ?_⟩
  exact Subtype.ext (congrArg Subtype.val hb)

theorem towerStageToQDegree_injective (s n : ℕ) (hn : n ≤ s) :
    Function.Injective (S.towerStageToQDegree k s n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨b, hb, he⟩ := a.property
  have hzero : Ideal.Quotient.mk (S.nonAperyIdeal k) b = 0 := by
    have h := congrArg Subtype.val ha
    change S.towerStageToQ k s a.val = 0 at h
    rw [← he] at h
    exact h
  have hN := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hF := S.lowDegree_nonApery_mem_jumpIdeal k s n hn b hb hN
  apply Subtype.ext
  rw [← he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hF

noncomputable def towerStageLowDegreeEquiv (s n : ℕ) (hn : n ≤ s) :
    S.towerStageDegree k s n ≃ₗ[k] S.qDegree k n :=
  LinearEquiv.ofBijective (S.towerStageToQDegree k s n)
    ⟨S.towerStageToQDegree_injective k s n hn, S.towerStageToQDegree_surjective k s n⟩

end NSP14.NumericalSemigroup
