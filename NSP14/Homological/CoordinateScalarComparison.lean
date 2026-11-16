module

public import NSP14.Homological.GradedScalarComparison
public import NSP14.Homological.CoordinateGradePieces

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ I : Type u) [Field k] [Field L] [Algebra k L]
variable (M : ModuleCat.{u} (VariableRing k σ)) (N : ModuleCat.{u} (VariableRing L σ))
variable (c : coefficientModule k σ M ≃ₗ[k] (I →₀ k))
variable (d : coefficientModule L σ N ≃ₗ[L] (I →₀ L)) (deg : I → ℤ)

/-- Compare independently specified coordinate gradings with the same true degree function.
All hypotheses concern actual degree inclusions and the specified coefficient map. -/
noncomputable def coordinateGradedScalarComparison
    (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N)
    (e : polynomialBaseChangeModule k L σ M ≅ N)
    (fk : ∀ q,G.piece q ≃ₗ[k] ({i : I // deg i=q} →₀ k))
    (fL : ∀ q,H.piece q ≃ₗ[L] ({i : I // deg i=q} →₀ L))
    (hk : ∀ q a,G.inclusion q a=coordinateDegreeInclusion k I deg σ M c q (fk q a))
    (hL : ∀ q a,H.inclusion q a=coordinateDegreeInclusion L I deg σ N d q (fL q a))
    (he : ∀ (a : coefficientModule k σ M) i,
      d (e.hom ((1:L) ⊗ₜ[k] a)) i=algebraMap k L (c a i)) :
    GradedScalarComparison k L σ G H e where
  pieceIso q := (LinearEquiv.baseChange k L _ _ (fk q)).trans
    ((coordinateGradeBaseChangeIso k I deg L q).trans (fL q).symm)
  inclusion_commutes q a := by
    apply d.injective
    ext i
    rw [hL,he,hk]
    simp only [LinearEquiv.trans_apply,LinearEquiv.baseChange_tmul,LinearEquiv.apply_symm_apply]
    rw [coordinateDegreeInclusion_coordinate,coordinateDegreeInclusion_coordinate]
    by_cases hi : deg i=q
    · simp [hi,coordinateGradeBaseChangeIso_tmul]
    · simp [hi]

end NSP14.Homological
