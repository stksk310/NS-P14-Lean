module

public import NSP14.Semigroup.TowerResources
public import NSP14.Semigroup.CoordinateSupport

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup


variable (S : NSP14.NumericalSemigroup)

def StageAlive (s : ℕ) (h : S.HeadExponent) : Prop :=
  ¬(h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s-1)

abbrev StageExponent (s : ℕ) := {h : S.HeadExponent // S.StageAlive s h}
abbrev StageDegreeExponent (s n : ℕ) := {h : S.StageExponent s // S.order h.val.val.val = n}

noncomputable instance stageExponentFintype (s : ℕ) : Fintype (S.StageExponent s) := by
  classical
  infer_instance

noncomputable instance stageDegreeExponentFintype (s n : ℕ) : Fintype (S.StageDegreeExponent s n) := by
  classical
  infer_instance

variable (k : Type*) [Field k]

noncomputable def stageProjection (s : ℕ) : S.HeadAlgebra k →ₗ[k] (S.StageExponent s →₀ k) :=
  (Finsupp.lsubtypeDomain {h | S.StageAlive s h}).comp (S.headQuotientEquiv k).toLinearMap

theorem stageProjection_ker (s : ℕ) :
    (S.stageProjection k s).ker = (S.jumpIdeal k (s-1)).restrictScalars k := by
  ext a
  rw [LinearMap.mem_ker]
  change Finsupp.subtypeDomain (S.StageAlive s) (S.headQuotientEquiv k a) = 0 ↔
    S.headQuotientEquiv k a ∈ Finsupp.supported k k _
  rw [Finsupp.subtypeDomain_eq_zero_iff',Finsupp.mem_supported']
  rfl

theorem stageProjection_surjective (s : ℕ) : Function.Surjective (S.stageProjection k s) := by
  intro f
  refine ⟨(S.headQuotientEquiv k).symm f.extendDomain,?_⟩
  change Finsupp.subtypeDomain _ (S.headQuotientEquiv k ((S.headQuotientEquiv k).symm _)) = f
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.subtypeDomain_extendDomain f

noncomputable def stageCoordinates (s : ℕ) : S.TowerStage k s ≃ₗ[k] (S.StageExponent s →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.stageProjection_ker k s).symm).trans
    ((S.stageProjection k s).quotKerEquivOfSurjective (S.stageProjection_surjective k s))

@[simp] theorem stageCoordinates_mk (s : ℕ) (a : S.HeadAlgebra k) :
    S.stageCoordinates k s (Ideal.Quotient.mk (S.jumpIdeal k (s-1)) a) = S.stageProjection k s a := rfl

theorem stageCoordinates_monomial (s : ℕ) (h : S.StageExponent s) :
    S.stageCoordinates k s (Ideal.Quotient.mk (S.jumpIdeal k (s-1)) (S.headBasis k h.val)) =
      Finsupp.single h 1 := by
  change Finsupp.subtypeDomain _ (S.headQuotientEquiv k (S.headBasis k h.val)) = _
  have he : S.headQuotientEquiv k (S.headBasis k h.val) = Finsupp.single h.val 1 := by
    simp [headBasis]
  rw [he]
  ext t
  change Finsupp.single h.val (1:k) t.val = Finsupp.single h (1:k) t
  by_cases ht : h = t
  · subst t; simp
  · have hv : h.val ≠ t.val := fun h' => ht (Subtype.ext h')
    simp [ht,hv]

theorem stageCoordinates_symm_single (s : ℕ) (h : S.StageExponent s) :
    (S.stageCoordinates k s).symm (Finsupp.single h 1) =
      Ideal.Quotient.mk (S.jumpIdeal k (s-1)) (S.headBasis k h.val) := by
  apply (S.stageCoordinates k s).injective
  rw [LinearEquiv.apply_symm_apply,S.stageCoordinates_monomial]

theorem towerStageDegree_coordinates (s n : ℕ) : S.towerStageDegree k s n =
    (Finsupp.supported k k {h : S.StageExponent s | S.order h.val.val.val = n}).comap
      (S.stageCoordinates k s).toLinearMap := by
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    change S.stageProjection k s b ∈ Finsupp.supported k k _
    rw [Finsupp.mem_supported']
    intro h hh
    exact (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k n b).1 hb) h.val hh
  · rw [NSP14.supported_comap_eq_span]
    apply Submodule.span_le.mpr
    rintro a ⟨h,hh,rfl⟩
    change (S.stageCoordinates k s).symm (Finsupp.single h 1) ∈ _
    rw [S.stageCoordinates_symm_single]
    refine ⟨S.headBasis k h.val,?_,rfl⟩
    rw [← S.headMonomial_eq_basis]
    exact S.headMonomial_mem_degree k h.val.val n hh

noncomputable def stageDegreeCoordinates (s n : ℕ) :
    S.towerStageDegree k s n ≃ₗ[k] (S.StageDegreeExponent s n →₀ k) where
  toFun a := Finsupp.subtypeDomain _ (S.stageCoordinates k s a.val)
  invFun f := ⟨(S.stageCoordinates k s).symm f.extendDomain,by
    rw [S.towerStageDegree_coordinates]
    change S.stageCoordinates k s ((S.stageCoordinates k s).symm f.extendDomain) ∈
      Finsupp.supported k k _
    rw [LinearEquiv.apply_symm_apply]
    exact f.support_extendDomain_subset⟩
  left_inv a := by
    apply Subtype.ext
    apply (S.stageCoordinates k s).injective
    rw [LinearEquiv.apply_symm_apply,Finsupp.extendDomain_subtypeDomain]
    exact (Finsupp.mem_supported k _).1 ((S.towerStageDegree_coordinates k s n).le a.property)
  right_inv f := by
    change Finsupp.subtypeDomain _ (S.stageCoordinates k s ((S.stageCoordinates k s).symm _)) = f
    rw [LinearEquiv.apply_symm_apply]
    exact Finsupp.subtypeDomain_extendDomain f
  map_add' a b := by
    simp only [Submodule.coe_add,map_add,Finsupp.subtypeDomain_add]
  map_smul' r a := by
    ext h
    change S.stageCoordinates k s (r • a.val) h.val = r • S.stageCoordinates k s a.val h.val
    rw [map_smul]
    rfl

noncomputable def stageDegreeBasis (s n : ℕ) : Module.Basis (S.StageDegreeExponent s n) k (S.towerStageDegree k s n) :=
  Finsupp.basisSingleOne.map (S.stageDegreeCoordinates k s n).symm

theorem towerStageDegree_finrank (s n : ℕ) :
    Module.finrank k (S.towerStageDegree k s n) = Fintype.card (S.StageDegreeExponent s n) :=
  Module.finrank_eq_card_basis (S.stageDegreeBasis k s n)

end NSP14.NumericalSemigroup
