module
public import NSP14.Homological.DirectSumSplit
public import NSP14.Homological.KoszulGradedMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]
  (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M) (xs : List σ)

theorem gradedKoszulInclusion_eq_sum (t : ℤ) :
    gradedKoszulInclusion k σ M G xs t=
      directSumInclusion k (gradedKoszulComplex k σ M G xs) t ≫ (gradedKoszulSumIso k σ M G xs).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (gradedKoszulSumPieceIso_inclusion k σ M G xs i t).symm

noncomputable def gradedKoszulRetraction (t : ℤ) :
    ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
      (koszulList k σ xs M) ⟶ gradedKoszulComplex k σ M G xs t :=
  (gradedKoszulSumIso k σ M G xs).inv ≫ directSumProjection k (gradedKoszulComplex k σ M G xs) t

@[reassoc]
theorem gradedKoszulInclusion_retraction (t : ℤ) :
    gradedKoszulInclusion k σ M G xs t ≫ gradedKoszulRetraction k σ M G xs t=𝟙 _ := by
  unfold gradedKoszulRetraction
  rw [gradedKoszulInclusion_eq_sum]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact directSumInclusion_projection k _ t

@[reassoc]
theorem gradedKoszulInclusion_retraction_ne (s t : ℤ) (hst : s ≠ t) :
    gradedKoszulInclusion k σ M G xs s ≫ gradedKoszulRetraction k σ M G xs t=0 := by
  unfold gradedKoszulRetraction
  rw [gradedKoszulInclusion_eq_sum]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact directSumInclusion_projection_ne k _ s t hst

/-- Internal-degree homology embeds into the same total actual homology.
The retraction is constructed at chain level, even for infinite chains. -/
theorem gradedKoszulHomologyInclusion_injective (t : ℤ) (i : ℕ) :
    Function.Injective (homologyMap (gradedKoszulInclusion k σ M G xs t) i) := by
  have hs := congrArg (fun f => homologyMap f i) (gradedKoszulInclusion_retraction k σ M G xs t)
  rw [homologyMap_comp,homologyMap_id] at hs
  intro a b hab
  have h := congrArg (fun z => (homologyMap (gradedKoszulRetraction k σ M G xs t) i).hom z) hab
  change (homologyMap (gradedKoszulInclusion k σ M G xs t) i ≫
    homologyMap (gradedKoszulRetraction k σ M G xs t) i).hom a =
      (homologyMap (gradedKoszulInclusion k σ M G xs t) i ≫
        homologyMap (gradedKoszulRetraction k σ M G xs t) i).hom b at h
  rw [hs] at h
  exact h

end NSP14.Homological
