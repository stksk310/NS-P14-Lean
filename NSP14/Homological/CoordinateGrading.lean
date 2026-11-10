module

public import NSP14.Homological.GradedModule

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k] (I : Type u) (deg : I → ℤ)

noncomputable def degreeFiberEquiv : (Σ q : ℤ,{i : I // deg i=q}) ≃ I where
  toFun a := a.2.val
  invFun i := ⟨deg i,⟨i,rfl⟩⟩
  left_inv a := by rcases a with ⟨q,i,h⟩; subst q; rfl
  right_inv _ := rfl

noncomputable def coordinateDegreeEquiv : (I →₀ k) ≃ₗ[k] (⨁ q : ℤ, {i : I // deg i=q} →₀ k) :=
  (Finsupp.domLCongr (degreeFiberEquiv I deg).symm).trans
    (sigmaFinsuppLequivDFinsupp k)

@[simp]
theorem coordinateDegreeEquiv_apply (f : I →₀ k) (q : ℤ) (i : {i : I // deg i=q}) :
    coordinateDegreeEquiv k I deg f q i=f i.val := by
  change (Finsupp.domLCongr (R := k) (M := k) (degreeFiberEquiv I deg).symm f) ⟨q,i⟩=f i.val
  simp [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,degreeFiberEquiv]

variable (σ : Type u) (M : ModuleCat.{u} (VariableRing k σ))
variable (c : coefficientModule k σ M ≃ₗ[k] (I →₀ k))

noncomputable def coordinateDegreeInclusion (q : ℤ) :
    ({i : I // deg i=q} →₀ k) →ₗ[k] coefficientModule k σ M :=
  c.symm.toLinearMap.comp ((coordinateDegreeEquiv k I deg).symm.toLinearMap.comp
    (DirectSum.lof k ℤ (fun q => {i : I // deg i=q} →₀ k) q))

theorem coordinateDegreeInclusion_range (q : ℤ) (a : coefficientModule k σ M) :
    a∈(coordinateDegreeInclusion k I deg σ M c q).range ↔
      ∀ i,deg i≠q → c a i=0 := by
  classical
  constructor
  · rintro ⟨b,rfl⟩ i hi
    have he := coordinateDegreeEquiv_apply k I deg
      (c (coordinateDegreeInclusion k I deg σ M c q b)) (deg i) ⟨i,rfl⟩
    simpa [coordinateDegreeInclusion,DirectSum.lof_eq_of,DirectSum.of_apply,Ne.symm hi] using he.symm
  · intro h
    refine ⟨coordinateDegreeEquiv k I deg (c a) q,?_⟩
    apply c.injective
    apply (coordinateDegreeEquiv k I deg).injective
    simp only [coordinateDegreeInclusion,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    ext r i
    by_cases hr : r=q
    · subst r; simp
    · have hi : deg i.val≠q := by simpa only [i.property] using hr
      simp [DirectSum.lof_eq_of,DirectSum.of_apply,Ne.symm hr,coordinateDegreeEquiv_apply,h i.val hi]

/-- Assemble the grading from true homogeneous variable actions in actual coordinates. -/
noncomputable def coordinateGrading
    (hv : ∀ (x : σ) (q : ℤ) (a : coefficientModule k σ M),
      (∀ i,deg i≠q → c a i=0) →
      ∀ i,deg i≠q+1 → c ((MvPolynomial.X x : VariableRing k σ) • a) i=0) :
    GradedPolynomialModule k σ M where
  piece q := ModuleCat.of k ({i : I // deg i=q} →₀ k)
  inclusion := coordinateDegreeInclusion k I deg σ M c
  sum_bijective := by
    have he : DirectSum.toModule k ℤ (coefficientModule k σ M)
        (coordinateDegreeInclusion k I deg σ M c) =
        c.symm.toLinearMap.comp (coordinateDegreeEquiv k I deg).symm.toLinearMap := by
      apply DirectSum.linearMap_ext
      intro q
      ext a
      simp [coordinateDegreeInclusion]
    rw [he]
    exact c.symm.bijective.comp (coordinateDegreeEquiv k I deg).symm.bijective
  variableMap x q := (DirectSum.component k ℤ _ (q+1)).comp
    ((coordinateDegreeEquiv k I deg).toLinearMap.comp (c.toLinearMap.comp
      ((coefficientMap k σ (ModuleCat.ofHom (X := M) (Y := M) (variableOperator k σ M x))).comp
        (coordinateDegreeInclusion k I deg σ M c q))))
  variable_commutes x q a := by
    apply c.injective
    apply (coordinateDegreeEquiv k I deg).injective
    ext r i
    simp only [coordinateDegreeInclusion,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    by_cases hr : r=q+1
    · subst r
      simp only [DirectSum.lof_apply]
      change coordinateDegreeEquiv k I deg
        (c ((MvPolynomial.X x : VariableRing k σ) • coordinateDegreeInclusion k I deg σ M c q a)) (q+1) i = _
      exact coordinateDegreeEquiv_apply k I deg _ _ _
    · have hi : deg i.val≠q+1 := by simpa only [i.property] using hr
      have ha : ∀ j,deg j≠q → c (coordinateDegreeInclusion k I deg σ M c q a) j=0 := by
        intro j hj
        have he := coordinateDegreeEquiv_apply k I deg
          (c (coordinateDegreeInclusion k I deg σ M c q a)) (deg j) ⟨j,rfl⟩
        simpa [coordinateDegreeInclusion,DirectSum.lof_eq_of,DirectSum.of_apply,Ne.symm hj] using he.symm
      have hz := hv x q _ ha i.val hi
      simp only [coordinateDegreeEquiv_apply,DirectSum.lof_eq_of,DirectSum.of_apply,dite_eq_right (Ne.symm hr),Finsupp.zero_apply]
      change 0 = c ((MvPolynomial.X x : VariableRing k σ) • coordinateDegreeInclusion k I deg σ M c q a) i.val
      exact hz.symm

/-- Restriction of the polynomial coefficient action agrees with the existing k-action. -/
noncomputable def coefficientOriginalEquiv (V : Type u) [AddCommGroup V] [Module k V]
    [Module (VariableRing k σ) V] [IsScalarTower k (VariableRing k σ) V] :
    coefficientModule k σ (ModuleCat.of (VariableRing k σ) V) ≃ₗ[k] V where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    change (algebraMap k (VariableRing k σ) r) • (show V from a) = (r • (show V from a) : V)
    exact algebraMap_smul (M := V) (VariableRing k σ) r a

noncomputable def natCoordinateGrading (d : I → ℕ)
    (hv : ∀ (x : σ) (p : ℕ) (a : coefficientModule k σ M),
      (∀ i,d i≠p → c a i=0) → ∀ i,d i≠p+1 → c ((MvPolynomial.X x : VariableRing k σ) • a) i=0) :
    GradedPolynomialModule k σ M :=
  coordinateGrading k I (fun i => (d i : ℤ)) σ M c (by
    intro x q a ha i hi
    by_cases hq : 0≤q
    · lift q to ℕ using hq
      exact hv x q a (fun j hj => ha j (by exact_mod_cast hj)) i (by exact_mod_cast hi)
    · have hz : a=0 := c.injective (by
        ext j
        simpa using ha j (by omega))
      rw [hz,smul_zero,map_zero,Finsupp.zero_apply])

/-- Use existing degree submodules; the resulting witness is tied to their actual coordinates. -/
noncomputable def actualCoordinateGrading (V : Type u) [AddCommGroup V] [Module k V]
    [Module (VariableRing k σ) V] [IsScalarTower k (VariableRing k σ) V]
    (d : I → ℕ) (cV : V ≃ₗ[k] (I →₀ k)) (D : ℕ → Submodule k V)
    (hc : ∀ p a,a∈D p ↔ ∀ i,d i≠p → cV a i=0)
    (hv : ∀ (x : σ) p (a : V),a∈D p → (MvPolynomial.X x : VariableRing k σ) • a∈D (p+1)) :
    GradedPolynomialModule k σ (ModuleCat.of (VariableRing k σ) V) :=
  natCoordinateGrading k I σ (ModuleCat.of (VariableRing k σ) V)
    ((coefficientOriginalEquiv k σ V).trans cV) d (by
      intro x p a ha i hi
      exact (hc (p+1) _).mp (hv x p a ((hc p a).mpr ha)) i hi)

end NSP14.Homological
