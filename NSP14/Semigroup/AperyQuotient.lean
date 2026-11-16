module

public import NSP14.Semigroup.NonAperyIdeal

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

def AperyExponent := {x : S.carrier // x.val ∈ S.aperySet}

noncomputable def aperyHeadEquiv :
    {x : S.HeadExponent // x.val.val ∈ S.aperySet} ≃ S.AperyExponent where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, S.apery_head x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Keep the actual Apéry coefficients of A. -/
noncomputable def aperyProjection : S.HeadAlgebra k →ₗ[k] (S.AperyExponent →₀ k) :=
  (Finsupp.domLCongr (R := k) (M := k) S.aperyHeadEquiv).toLinearMap.comp
    ((Finsupp.lsubtypeDomain {x : S.HeadExponent | x.val.val ∈ S.aperySet}).comp
      (S.headQuotientEquiv k).toLinearMap)

theorem aperyProjection_apply (a : S.HeadAlgebra k) (x : S.AperyExponent) :
    S.aperyProjection k a x = S.headQuotientEquiv k a ⟨x.val, S.apery_head x.property⟩ := by
  simp [aperyProjection, Finsupp.domLCongr_apply, aperyHeadEquiv]
  rfl

theorem aperyProjection_ker : (S.aperyProjection k).ker = (S.nonAperyIdeal k).restrictScalars k := by
  ext a
  rw [LinearMap.mem_ker]
  change S.aperyProjection k a = 0 ↔ a ∈ S.nonAperySpace k
  rw [S.mem_nonAperySpace]
  constructor
  · intro h x hx
    have he := congrArg (fun g : S.AperyExponent →₀ k => g ⟨x.val, hx⟩) h
    exact (S.aperyProjection_apply k a ⟨x.val, hx⟩).symm.trans he
  · intro h
    ext x
    rw [S.aperyProjection_apply]
    exact h _ x.property

theorem aperyProjection_surjective : Function.Surjective (S.aperyProjection k) := by
  intro f
  let g := (Finsupp.domLCongr (R := k) (M := k) S.aperyHeadEquiv).symm f
  refine ⟨(S.headQuotientEquiv k).symm g.extendDomain, ?_⟩
  simp only [aperyProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.lsubtypeDomain_apply,
    Finsupp.subtypeDomain_extendDomain]
  exact (Finsupp.domLCongr (R := k) (M := k) S.aperyHeadEquiv).apply_symm_apply f

/-- The actual quotient A/N, not a coordinate space used as its definition. -/
abbrev AperyAlgebra := S.HeadAlgebra k ⧸ S.nonAperyIdeal k

noncomputable def aperyQuotientEquiv : S.AperyAlgebra k ≃ₗ[k] (S.AperyExponent →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.aperyProjection_ker k).symm).trans
    ((S.aperyProjection k).quotKerEquivOfSurjective (S.aperyProjection_surjective k))

noncomputable def aperyQuotientBasis : Module.Basis S.AperyExponent k (S.AperyAlgebra k) :=
  Finsupp.basisSingleOne.map (S.aperyQuotientEquiv k).symm

noncomputable def qMonomial (x : S.carrier) : S.AperyAlgebra k :=
  Ideal.Quotient.mk (S.nonAperyIdeal k) (S.headMonomial k x)

theorem aperyQuotientEquiv_mk (a : S.HeadAlgebra k) :
    S.aperyQuotientEquiv k (Ideal.Quotient.mk (S.nonAperyIdeal k) a) = S.aperyProjection k a := rfl

theorem qMonomial_coordinates (x : S.carrier) (y : S.AperyExponent) :
    S.aperyQuotientEquiv k (S.qMonomial k x) y = Finsupp.single x (1 : k) y.val := by
  rw [qMonomial, S.aperyQuotientEquiv_mk]
  exact (S.aperyProjection_apply k (S.headMonomial k x) y).trans
    (S.headMonomial_coordinates k x ⟨y.val, S.apery_head y.property⟩)

theorem aperyQuotientEquiv_initial (x : S.AperyExponent) :
    S.aperyQuotientEquiv k (S.qMonomial k x.val) = Finsupp.single x 1 := by
  ext y
  rw [S.qMonomial_coordinates]
  by_cases h : x = y
  · subst y; simp
  · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
    simp [h, hv]

theorem aperyQuotientBasis_eq_initial (x : S.AperyExponent) :
    S.aperyQuotientBasis k x = S.qMonomial k x.val := by
  apply (S.aperyQuotientEquiv k).injective
  rw [S.aperyQuotientEquiv_initial]
  simp [aperyQuotientBasis]

theorem qMonomial_zero_of_nonapery (x : S.carrier) (hx : x.val ∉ S.aperySet) :
    S.qMonomial k x = 0 := by
  apply (S.aperyQuotientEquiv k).injective
  ext y
  rw [S.qMonomial_coordinates, map_zero]
  have hxy : x ≠ y.val := by intro he; exact hx (he ▸ y.property)
  simp [hxy]

theorem qMonomial_ne_zero (x : S.AperyExponent) : S.qMonomial k x.val ≠ 0 := by
  intro h
  have he := congrArg (S.aperyQuotientEquiv k) h
  rw [S.aperyQuotientEquiv_initial, map_zero] at he
  exact Finsupp.single_ne_zero.mpr one_ne_zero he

theorem qMonomial_mul_live (x y : S.carrier)
    (h : S.order (x.val + y.val) = S.order x.val + S.order y.val) :
    S.qMonomial k x * S.qMonomial k y = S.qMonomial k (x + y) := by
  rw [qMonomial, qMonomial, ← map_mul, S.headMonomial_mul_live k x y h]
  rfl

theorem qMonomial_mul_dead (x y : S.carrier)
    (h : S.order x.val + S.order y.val < S.order (x.val + y.val)) :
    S.qMonomial k x * S.qMonomial k y = 0 := by
  rw [qMonomial, qMonomial, ← map_mul, S.headMonomial_mul_dead k x y h, map_zero]

end NSP14.NumericalSemigroup
