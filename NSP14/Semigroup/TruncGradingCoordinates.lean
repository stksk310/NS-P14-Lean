module
public import NSP14.Semigroup.TruncCoordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type*) [Field k]

abbrev HighStageExponent (s n : ℕ) := {h : S.StageExponent s // n ≤ S.order h.val.val.val}

noncomputable def truncCoordinates (s n : ℕ) :
    ↥(S.towerHighIdeal k s n) ≃ₗ[k] (S.HighStageExponent s n →₀ k) where
  toFun a := Finsupp.subtypeDomain _ (S.stageCoordinates k s a.val)
  invFun f := ⟨(S.stageCoordinates k s).symm f.extendDomain,by
    change (S.stageCoordinates k s).symm f.extendDomain ∈ (S.towerHighIdeal k s n).restrictScalars k
    rw [S.towerHigh_coordinates]
    change S.stageCoordinates k s ((S.stageCoordinates k s).symm f.extendDomain) ∈ Finsupp.supported k k _
    rw [LinearEquiv.apply_symm_apply]
    exact f.support_extendDomain_subset⟩
  left_inv a := by
    apply Subtype.ext
    apply (S.stageCoordinates k s).injective
    rw [LinearEquiv.apply_symm_apply,Finsupp.extendDomain_subtypeDomain]
    exact (Finsupp.mem_supported k _).1 ((S.towerHigh_coordinates k s n).le a.property)
  right_inv f := by
    change Finsupp.subtypeDomain _ (S.stageCoordinates k s ((S.stageCoordinates k s).symm _))=f
    rw [LinearEquiv.apply_symm_apply]
    exact Finsupp.subtypeDomain_extendDomain f
  map_add' a b := by
    simp only [Submodule.coe_add,map_add,Finsupp.subtypeDomain_add]
  map_smul' r a := by
    ext h
    change S.stageCoordinates k s (r • a.val) h.val=r • S.stageCoordinates k s a.val h.val
    rw [map_smul]
    rfl

theorem truncDegree_coordinates (s n p : ℕ) (a : ↥(S.towerHighIdeal k s n)) :
    a.val ∈ S.towerStageDegree k s p ↔
      ∀ h : S.HighStageExponent s n,S.order h.val.val.val.val ≠ p → S.truncCoordinates k s n a h=0 := by
  rw [S.towerStageDegree_coordinates]
  change S.stageCoordinates k s a.val ∈ Finsupp.supported k k _ ↔ _
  rw [Finsupp.mem_supported']
  constructor
  · intro ha h hh
    simpa only [truncCoordinates,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
      Finsupp.subtypeDomain_apply] using ha h.val hh
  · intro ha h hh
    by_cases hn : n ≤ S.order h.val.val.val
    · simpa only [truncCoordinates,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
        Finsupp.subtypeDomain_apply] using ha ⟨h,hn⟩ hh
    · have hu := (S.towerHigh_coordinates k s n).le a.property
      exact (Finsupp.mem_supported' k _).1 hu h hn
end NSP14.NumericalSemigroup
