module

public import NSP14.Homological.KoszulGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]
variable (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M) (xs : List σ)

noncomputable def gradedKoszulSpace (t : ℤ) (i : ℕ) :
    Submodule k (coefficientModule k σ ((koszulList k σ xs M).X i)) :=
  (koszulChainGrading k σ M G xs i).degreeSpace (t-(i:ℤ))

noncomputable def gradedKoszulDifferential (t : ℤ) (i : ℕ) :
    gradedKoszulSpace k σ M G xs t (i+1) →ₗ[k] gradedKoszulSpace k σ M G xs t i :=
  LinearMap.codRestrict _ ((coefficientMap k σ ((koszulList k σ xs M).d (i+1) i)).comp
    (gradedKoszulSpace k σ M G xs t (i+1)).subtype) (fun a => by
      have h := koszul_d_homogeneous k σ M G xs i (t-((i+1:ℕ):ℤ)) a.val a.property
      have he : t-((i+1:ℕ):ℤ)+1=t-(i:ℤ) := by omega
      change (koszulList k σ xs M).d (i+1) i a.val ∈
        (koszulChainGrading k σ M G xs i).degreeSpace (t-(i:ℤ))
      rw [← he]
      exact h)

/-- The internal degree t summand of the same actual signed Koszul differential. -/
noncomputable def gradedKoszulComplex (t : ℤ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (gradedKoszulSpace k σ M G xs t i))
    (fun i => ModuleCat.ofHom (gradedKoszulDifferential k σ M G xs t i)) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      change (koszulList k σ xs M).d (i+1) i ((koszulList k σ xs M).d (i+1+1) (i+1) a.val)=0
      rw [← ModuleCat.comp_apply,(koszulList k σ xs M).d_comp_d]
      rfl)

/-- The literal inclusions of each internal-degree complex into the actual complex. -/
noncomputable def gradedKoszulInclusion (t : ℤ) :
    gradedKoszulComplex k σ M G xs t ⟶
      ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
        (koszulList k σ xs M) :=
  ChainComplex.ofHom (fun i => ModuleCat.ofHom
    (X := ModuleCat.of k (gradedKoszulSpace k σ M G xs t i))
    (Y := coefficientModule k σ ((koszulList k σ xs M).X i))
    (gradedKoszulSpace k σ M G xs t i).subtype) (by
    intro i
    simp only [gradedKoszulComplex,ChainComplex.of_d]
    apply ModuleCat.hom_ext
    ext a
    rfl)

end NSP14.Homological
