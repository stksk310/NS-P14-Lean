module
public import NSP14.Homological.KoszulGrading
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped DirectSum Classical
namespace NSP14.Homological
universe u v
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
  (G : GradedPolynomialModule k σ M)

theorem graded_decomposition_inclusion (q : ℤ) (a : G.piece q) :
    (GradedPolynomialModule.decomposition k σ G) (G.inclusion q a)=DirectSum.lof k ℤ (fun q => G.piece q) q a := by
  apply (GradedPolynomialModule.decomposition k σ G).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change G.inclusion q a=DirectSum.toModule k ℤ (coefficientModule k σ M) G.inclusion _
  rw [DirectSum.toModule_lof]

noncomputable def gradedProjection (q : ℤ) : coefficientModule k σ M →ₗ[k] coefficientModule k σ M :=
  (G.inclusion q).comp ((DirectSum.component k ℤ (fun q => G.piece q) q).comp (GradedPolynomialModule.decomposition k σ G).toLinearMap)

theorem gradedProjection_inclusion (q p : ℤ) (a : G.piece p) :
    gradedProjection k σ M G q (G.inclusion p a)=if p=q then G.inclusion p a else 0 := by
  simp only [gradedProjection,LinearMap.comp_apply,LinearEquiv.coe_coe,graded_decomposition_inclusion]
  by_cases h : p=q
  · subst p
    simp
  · simp only [DirectSum.component.of,dite_eq_right h,map_zero,ite_eq_right h]

theorem gradedProjection_eq_self (q : ℤ) (a : coefficientModule k σ M) (ha : a ∈ G.degreeSpace q) :
    gradedProjection k σ M G q a=a := by
  obtain ⟨b,rfl⟩ := ha
  rw [gradedProjection_inclusion,ite_eq_left rfl]

variable {J : Type v} (B : Module.Basis J k (coefficientModule k σ M))
  (deg : J → ℤ) (hB : ∀ i,B i ∈ G.degreeSpace (deg i))
include hB

theorem gradedProjection_basis (q : ℤ) (i : J) :
    gradedProjection k σ M G q (B i)=if deg i=q then B i else 0 := by
  obtain ⟨a,ha⟩ := hB i
  rw [← ha,gradedProjection_inclusion]

/-- Coordinates of an actual homogeneous vector vanish outside its degree.
No finite-dimensionality, or initial-module assumption, is hidden here. -/
theorem gradedBasis_repr_zero (q : ℤ) (a : coefficientModule k σ M)
    (ha : a ∈ G.degreeSpace q) (i : J) (hi : deg i ≠ q) : B.repr a i=0 := by
  have hm : (B.coord i).comp (gradedProjection k σ M G q)=0 := by
    apply B.ext
    intro j
    change B.repr (gradedProjection k σ M G q (B j)) i=0
    rw [gradedProjection_basis k σ M G B deg hB]
    by_cases hj : deg j=q
    · rw [ite_eq_left hj]
      have hji : j ≠ i := fun h => hi (by simpa only [h] using hj)
      simp only [Module.Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hji)]
    · rw [ite_eq_right hj,map_zero,Finsupp.zero_apply]
  have h := LinearMap.congr_fun hm a
  rw [LinearMap.comp_apply,gradedProjection_eq_self k σ M G q a ha] at h
  exact h

theorem gradedBasis_degreeSpace_eq_span (q : ℤ) :
    G.degreeSpace q=Submodule.span k (B '' {i | deg i=q}) := by
  apply le_antisymm
  · intro a ha
    apply B.mem_span_image.mpr
    intro i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (gradedBasis_repr_zero k σ M G B deg hB q a ha i hn)
  · apply Submodule.span_le.mpr
    rintro a ⟨i,hi,rfl⟩
    rw [← (show deg i=q from hi)]
    exact hB i

/-- The Hilbert function is the number of actual standard-basis labels in
that degree; it is not a supplied dimension-preservation assumption. -/
theorem gradedBasis_piece_finrank [Module.Finite k (coefficientModule k σ M)] (q : ℤ) :
    Module.finrank k (G.piece q)=Nat.card {i : J //deg i=q} := by
  have : Finite J := B.linearIndependent.finite
  let : Fintype J := Fintype.ofFinite _
  let : Fintype {i : J //deg i=q} := Fintype.ofFinite _
  let f : {i : J //deg i=q} → coefficientModule k σ M := fun i => B i.val
  have hli : LinearIndependent k f := B.linearIndependent.comp Subtype.val Subtype.val_injective
  have hs : Set.range f=B '' {i | deg i=q} := by
    ext a
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have hp := finrank_span_eq_card hli
  rw [hs,← gradedBasis_degreeSpace_eq_span k σ M G B deg hB] at hp
  have he := (LinearEquiv.ofInjective (G.inclusion q) (G.inclusion_injective k σ q)).finrank_eq
  change Module.finrank k (G.piece q)=Module.finrank k (G.degreeSpace q) at he
  rw [he,hp,Nat.card_eq_fintype_card]
end NSP14.Homological
