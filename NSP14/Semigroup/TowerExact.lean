module
public import NSP14.Semigroup.HighIdeal
public import NSP14.Semigroup.CutAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def towerStep (s : ℕ) :
    S.TowerStage k s →ₐ[S.PolynomialRing k] S.TowerStage k (s+1) :=
  Ideal.Quotient.factorₐ (S.PolynomialRing k) (S.jumpIdeal_monotone k (Nat.sub_le s 1))

@[simp] theorem towerStep_mk (s : ℕ) (a : S.HeadAlgebra k) :
    S.towerStep k s (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

noncomputable def towerKIdeal (s : ℕ) : Ideal (S.TowerStage k s) :=
  (S.jumpIdeal k s).map (Ideal.Quotient.mk (S.jumpIdeal k (s-1)))
abbrev TowerK (s : ℕ) := ↥(S.towerKIdeal k s)

theorem towerStep_zero_iff (s : ℕ) (a : S.TowerStage k s) :
    S.towerStep k s a=0 ↔ a ∈ S.towerKIdeal k s := by
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [S.towerStep_mk,Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.mem_quotient_iff_mem (S.jumpIdeal_monotone k (Nat.sub_le s 1))).symm

/-- F_s/F_{s-1} embeds in degree≥s+1, because a terminal has positive degree. -/
theorem towerK_le_high (s : ℕ) (hs : 1 ≤ s) :
    S.towerKIdeal k s ≤ S.towerHighIdeal k s (s+1) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
  have hsupport : ∀ h ∈ (S.headQuotientEquiv k b).support,
      h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s :=
    (Finsupp.mem_supported k _).1 hb
  rw [← S.head_expansion k b,Finsupp.sum]
  change (Ideal.Quotient.mkₐ k (S.jumpIdeal k (s-1))).toLinearMap (∑ h ∈ (S.headQuotientEquiv k b).support, (S.headQuotientEquiv k b h) • S.headBasis k h) ∈ _
  rw [map_sum]
  apply (S.towerHighIdeal k s (s+1)).sum_mem
  intro h hh
  rw [map_smul]
  apply ((S.towerHighIdeal k s (s+1)).restrictScalars k).smul_mem
  obtain ⟨hn,hj⟩ := hsupport h hh
  by_cases hlow : S.jump (h.val.val-S.multiplicity) ≤ s-1
  · have hmem : S.headBasis k h ∈ S.jumpIdeal k (s-1) := by
      rw [← S.headMonomial_eq_basis k h]
      exact S.head_mem_jumpASpace k (s-1) h.val hn hlow
    change Ideal.Quotient.mk _ (S.headBasis k h) ∈ S.towerHighIdeal k s (s+1)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    exact Ideal.zero_mem _
  · have ht := S.head_sub_terminal (⟨h.property,hn⟩ : S.NonAperyHead h.val.val)
    have hp := S.order_pos ht.1 (S.terminal_pos ht)
    have he : h.val.val-S.multiplicity+S.multiplicity=h.val.val := by
      obtain ⟨x,hx,he⟩ := S.head_predecessor (⟨h.property,hn⟩ : S.NonAperyHead h.val.val)
      omega
    have ho : S.order h.val.val = S.order (h.val.val-S.multiplicity)+S.jump (h.val.val-S.multiplicity) := by
      unfold jump
      rw [he]
      have hh := S.order_add_multiplicity ht.1
      rw [he] at hh
      omega
    exact Ideal.mem_map_of_mem _ (S.headBasis_mem_highSpace k (s+1) h (by omega))

noncomputable def towerKInclusion (s : ℕ) (hs : 1 ≤ s) :
    S.TowerK k s →ₗ[S.PolynomialRing k] S.TowerM k s where
  toFun a := ⟨a.val,S.towerK_le_high k s hs a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def towerTruncStep (s n : ℕ) :
    ↥(S.towerHighIdeal k s n) →ₗ[S.PolynomialRing k] ↥(S.towerHighIdeal k (s+1) n) where
  toFun a := ⟨S.towerStep k s a.val,by
    obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property
    rw [← he,S.towerStep_mk]
    exact Ideal.mem_map_of_mem _ hb⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext ((S.towerStep k s).toLinearMap.map_smul r a.val)

theorem towerTruncStep_surjective (s n : ℕ) : Function.Surjective (S.towerTruncStep k s n) := by
  intro a
  obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property
  exact ⟨⟨Ideal.Quotient.mk _ b,Ideal.mem_map_of_mem _ hb⟩,Subtype.ext he⟩

/-- The actual tower sequence is exact already over S₀, hence also over the
one fixed P by restriction. -/
theorem tower_exact (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (S.towerKInclusion k s hs) ∧
    Function.Exact (S.towerKInclusion k s hs) (S.towerTruncStep k s (s+1)) ∧
    Function.Surjective (S.towerTruncStep k s (s+1)) := by
  refine ⟨fun a b he => Subtype.ext (congrArg (fun x : S.TowerM k s => x.val) he),?_,S.towerTruncStep_surjective k s (s+1)⟩
  intro a
  constructor
  · intro ha
    have hz : S.towerStep k s a.val=0 := congrArg Subtype.val ha
    exact ⟨⟨a.val,(S.towerStep_zero_iff k s a.val).1 hz⟩,Subtype.ext rfl⟩
  · rintro ⟨b,rfl⟩
    apply Subtype.ext
    exact (S.towerStep_zero_iff k s b.val).2 b.property

end NSP14.NumericalSemigroup
