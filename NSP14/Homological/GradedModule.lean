module

public import NSP14.Homological.DirectSumHomology
public import NSP14.Homological.PolynomialBaseChangeFunctor
public import Mathlib.Data.Finsupp.ToDFinsupp

@[expose] public section

open CategoryTheory
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- Direct sums distribute over products, with the actual two component projections. -/
noncomputable def directSumProductEquiv (A B : ℤ → ModuleCat.{u} k) :
    (⨁ q, A q × B q) ≃ₗ[k] (⨁ q,A q) × (⨁ q,B q) where
  toLinearMap := (DirectSum.lmap (fun q => LinearMap.fst k (A q) (B q))).prod
    (DirectSum.lmap (fun q => LinearMap.snd k (A q) (B q)))
  invFun p := DirectSum.lmap (fun q => LinearMap.inl k (A q) (B q)) p.1 +
    DirectSum.lmap (fun q => LinearMap.inr k (A q) (B q)) p.2
  left_inv p := by ext q <;> simp
  right_inv p := by apply Prod.ext <;> ext q <;> simp

variable (σ : Type u)

/-- A genuine grading witness on an actual polynomial module. Its variable maps are
restrictions of actual X-actions, and its direct sum is the actual coefficient module. -/
structure GradedPolynomialModule (M : ModuleCat.{u} (VariableRing k σ)) where
  piece : ℤ → ModuleCat.{u} k
  inclusion : ∀ q,piece q →ₗ[k] coefficientModule k σ M
  sum_bijective : Function.Bijective (DirectSum.toModule k ℤ (coefficientModule k σ M) inclusion)
  variableMap : σ → ∀ q,piece q →ₗ[k] piece (q+1)
  variable_commutes : ∀ (_x : σ) q (a : piece q),
    inclusion (q+1) (variableMap _x q a) = (MvPolynomial.X _x : VariableRing k σ) • inclusion q a

noncomputable def GradedPolynomialModule.decomposition
    {M : ModuleCat.{u} (VariableRing k σ)} (G : GradedPolynomialModule k σ M) :
    coefficientModule k σ M ≃ₗ[k] (⨁ q,G.piece q) :=
  (LinearEquiv.ofBijective (DirectSum.toModule k ℤ (coefficientModule k σ M) G.inclusion) G.sum_bijective).symm

theorem GradedPolynomialModule.inclusion_injective
    {M : ModuleCat.{u} (VariableRing k σ)} (G : GradedPolynomialModule k σ M) (q : ℤ) :
    Function.Injective (G.inclusion q) := by
  classical
  intro a b h
  have he : DirectSum.lof k ℤ (fun q => G.piece q) q a =
      DirectSum.lof k ℤ (fun q => G.piece q) q b := G.sum_bijective.1 (by simpa using h)
  simpa using congrArg (fun z => z q) he

noncomputable def coefficientProductEquiv (M N : ModuleCat.{u} (VariableRing k σ)) :
    coefficientModule k σ (ModuleCat.of (VariableRing k σ) (M × N)) ≃ₗ[k]
      (coefficientModule k σ M × coefficientModule k σ N) where
  toFun a := (a.1,a.2)
  invFun a := (a.1,a.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem directSum_toModule_bijective_reindex (A : ℤ → ModuleCat.{u} k)
    (V : ModuleCat.{u} k) (f : ∀ q,A q →ₗ[k] V)
    (hf : Function.Bijective (DirectSum.toModule k ℤ V f)) (h : ℤ ≃ ℤ) :
    Function.Bijective (DirectSum.toModule k ℤ V (fun t => f (h t))) := by
  classical
  let e := DirectSum.lequivCongrLeft k (M := fun q => A q) h.symm
  have he : DirectSum.toModule k ℤ V (fun t => f (h t)) =
      (DirectSum.toModule k ℤ V f).comp e.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro t
    ext a
    simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearEquiv.coe_coe]
    change f (h t) a = DirectSum.toModule k ℤ V f (e.symm (DirectSum.lof k ℤ (fun t => A (h t)) t a))
    dsimp only [e]
    erw [DirectSum.lequivCongrLeft_symm_lof (R := k) (M := fun q => A q) (h := h.symm)]
    simp
  rw [he]
  exact hf.comp e.symm.bijective

namespace GradedPolynomialModule

variable {k σ} {M N : ModuleCat.{u} (VariableRing k σ)}

/-- Transport a grading by an actual polynomial-linear isomorphism. -/
noncomputable def transport (G : GradedPolynomialModule k σ M) (e : M ≅ N) :
    GradedPolynomialModule k σ N where
  piece := G.piece
  inclusion q := (coefficientMap k σ e.hom).comp (G.inclusion q)
  sum_bijective := by
    have he : DirectSum.toModule k ℤ (coefficientModule k σ N)
        (fun q => (coefficientMap k σ e.hom).comp (G.inclusion q)) =
        (coefficientMap k σ e.hom).comp (DirectSum.toModule k ℤ (coefficientModule k σ M) G.inclusion) := by
      apply DirectSum.linearMap_ext
      intro q
      ext a
      simp
    rw [he]
    exact ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso e).toLinearEquiv.bijective.comp
      G.sum_bijective
  variableMap := G.variableMap
  variable_commutes x q a := by
    change coefficientMap k σ e.hom (G.inclusion (q+1) (G.variableMap x q a)) = _
    rw [G.variable_commutes]
    exact e.hom.hom.map_smul _ _

/-- Product grading; no finiteness of the underlying coefficient spaces is assumed. -/
noncomputable def prod (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule k σ N) :
    GradedPolynomialModule k σ (ModuleCat.of (VariableRing k σ) (M × N)) where
  piece q := ModuleCat.of k (G.piece q × H.piece q)
  inclusion q := (coefficientProductEquiv k σ M N).symm.toLinearMap.comp
    ((G.inclusion q).prodMap (H.inclusion q))
  sum_bijective := by
    let e := (directSumProductEquiv k G.piece H.piece).trans
      (G.decomposition.symm.prodCongr H.decomposition.symm) |>.trans (coefficientProductEquiv k σ M N).symm
    have he : DirectSum.toModule k ℤ (coefficientModule k σ (ModuleCat.of (VariableRing k σ) (M×N)))
        (fun q => (coefficientProductEquiv k σ M N).symm.toLinearMap.comp
          ((G.inclusion q).prodMap (H.inclusion q))) = e.toLinearMap := by
      apply DirectSum.linearMap_ext
      intro q
      ext a <;> simp [e,directSumProductEquiv,decomposition,coefficientProductEquiv]
    rw [he]
    exact e.bijective
  variableMap x q := (G.variableMap x q).prodMap (H.variableMap x q)
  variable_commutes x q a := by
    apply Prod.ext
    · exact G.variable_commutes x q a.1
    · exact H.variable_commutes x q a.2

noncomputable def zero (M : ModuleCat.{u} (VariableRing k σ)) (hM : Limits.IsZero M) :
    GradedPolynomialModule k σ M where
  piece _ := ModuleCat.of k PUnit
  inclusion _ := 0
  sum_bijective := by
    let : Subsingleton (coefficientModule k σ M) := (show Subsingleton M from ModuleCat.subsingleton_of_isZero hM)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun _ => ⟨0,Subsingleton.elim _ _⟩⟩
  variableMap _ _ := 0
  variable_commutes _ _ _ := by simp

noncomputable def rangeEquiv (G : GradedPolynomialModule k σ M) (q : ℤ) :
    G.piece q ≃ₗ[k] (G.inclusion q).range :=
  LinearEquiv.ofInjective (G.inclusion q) (inclusion_injective k σ G q)

theorem degreeSum_bijective (G : GradedPolynomialModule k σ M) :
    Function.Bijective (DirectSum.toModule k ℤ (coefficientModule k σ M)
      (fun q => (G.inclusion q).range.subtype)) := by
  let e := DirectSum.congrLinearEquiv (fun q => (G.rangeEquiv q).symm)
  have he : DirectSum.toModule k ℤ (coefficientModule k σ M)
      (fun q => (G.inclusion q).range.subtype) =
      (DirectSum.toModule k ℤ (coefficientModule k σ M) G.inclusion).comp e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro q
    ext a
    simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearEquiv.coe_coe]
    change a.val = DirectSum.toModule k ℤ (coefficientModule k σ M) G.inclusion
      (DirectSum.lmap (fun q => (G.rangeEquiv q).symm.toLinearMap) (DirectSum.lof k ℤ _ q a))
    rw [DirectSum.lmap_lof,DirectSum.toModule_lof]
    have he := congrArg Subtype.val ((G.rangeEquiv q).apply_symm_apply a)
    change G.inclusion q ((G.rangeEquiv q).symm a) = a.val at he
    exact he.symm
  rw [he]
  exact G.sum_bijective.comp e.bijective

end GradedPolynomialModule

end NSP14.Homological
