module
public import NSP14.Semigroup.HighIdeal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type*) [Field k]

theorem towerHigh_coordinates (s n : ℕ) :
    (S.towerHighIdeal k s n).restrictScalars k =
      (Finsupp.supported k k {h : S.StageExponent s | n ≤ S.order h.val.val.val}).comap
        (S.stageCoordinates k s).toLinearMap := by
  apply le_antisymm
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
    change Finsupp.subtypeDomain _ (S.headQuotientEquiv k b) ∈ Finsupp.supported k k _
    rw [Finsupp.mem_supported']
    intro h hh
    exact (Finsupp.mem_supported' k _).1 hb h.val hh
  · rw [NSP14.supported_comap_eq_span]
    apply Submodule.span_le.mpr
    rintro a ⟨h,hh,rfl⟩
    change (S.stageCoordinates k s).symm (Finsupp.single h 1) ∈ _
    rw [S.stageCoordinates_symm_single]
    exact Ideal.mem_map_of_mem _ (S.headBasis_mem_highSpace k n h.val hh)

noncomputable def truncBottomProjection (s n : ℕ) :
    ↥(S.towerHighIdeal k s n) →ₗ[k] (S.StageDegreeExponent s n →₀ k) :=
  (Finsupp.lsubtypeDomain {h : S.StageExponent s | S.order h.val.val.val=n}).comp
    ((S.stageCoordinates k s).toLinearMap.comp ((S.towerHighIdeal k s n).restrictScalars k).subtype)

noncomputable def truncNextSpace (s n : ℕ) : Submodule k ↥(S.towerHighIdeal k s n) :=
  ((S.towerHighIdeal k s (n+1)).restrictScalars k).comap
    ((S.towerHighIdeal k s n).restrictScalars k).subtype

theorem truncBottomProjection_ker (s n : ℕ) :
    (S.truncBottomProjection k s n).ker = S.truncNextSpace k s n := by
  ext a
  have ha := (S.towerHigh_coordinates k s n).le a.property
  change S.stageCoordinates k s a.val ∈ Finsupp.supported k k _ at ha
  rw [LinearMap.mem_ker]
  change Finsupp.subtypeDomain _ (S.stageCoordinates k s a.val)=0 ↔
    a.val ∈ S.towerHighIdeal k s (n+1)
  rw [Finsupp.subtypeDomain_eq_zero_iff']
  change (∀ h, S.order h.val.val.val=n → S.stageCoordinates k s a.val h=0) ↔ _
  have hc : a.val ∈ S.towerHighIdeal k s (n+1) ↔
      S.stageCoordinates k s a.val ∈ Finsupp.supported k k {h : S.StageExponent s | n+1 ≤ S.order h.val.val.val} :=
    SetLike.ext_iff.mp (S.towerHigh_coordinates k s (n+1)) a.val
  rw [hc]
  rw [Finsupp.mem_supported']
  constructor
  · intro hz h hh
    by_cases hlow : n ≤ S.order h.val.val.val
    · apply hz h
      change ¬n+1 ≤ S.order h.val.val.val at hh
      omega
    · exact (Finsupp.mem_supported' k _).1 ha h hlow
  · intro hz h hh
    exact hz h (by change ¬n+1 ≤ S.order h.val.val.val; omega)

theorem truncBottomProjection_surjective (s n : ℕ) : Function.Surjective (S.truncBottomProjection k s n) := by
  intro f
  let a : S.towerStageDegree k s n := (S.stageDegreeCoordinates k s n).symm f
  refine ⟨⟨a.val,S.towerStageDegree_le_high k s n n le_rfl a.property⟩,?_⟩
  exact (S.stageDegreeCoordinates k s n).apply_symm_apply f

/-- The actual bottom-degree quotient; its dimension is the actual number
of homogeneous generators in the prescribed degree. -/
noncomputable def truncGeneratorQuotientEquiv (s n : ℕ) :
    (↥(S.towerHighIdeal k s n) ⧸ S.truncNextSpace k s n) ≃ₗ[k] S.towerStageDegree k s n :=
  ((Submodule.quotEquivOfEq _ _ (S.truncBottomProjection_ker k s n).symm).trans
    ((S.truncBottomProjection k s n).quotKerEquivOfSurjective (S.truncBottomProjection_surjective k s n))).trans
      (S.stageDegreeCoordinates k s n).symm

theorem trunc_generator_count (s n : ℕ) :
    Module.finrank k (↥(S.towerHighIdeal k s n) ⧸ S.truncNextSpace k s n) =
      Module.finrank k (S.towerStageDegree k s n) := (S.truncGeneratorQuotientEquiv k s n).finrank_eq

end NSP14.NumericalSemigroup
