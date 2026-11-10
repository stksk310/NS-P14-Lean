module

public import NSP14.Homological.GradedKoszulComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]
variable (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M) (xs : List σ)

theorem gradedKoszul_sum_bijective (i : ℕ) :
    Function.Bijective (DirectSum.toModule k ℤ (coefficientModule k σ ((koszulList k σ xs M).X i))
      (fun t => (gradedKoszulSpace k σ M G xs t i).subtype)) := by
  exact directSum_toModule_bijective_reindex k
    (fun q => ModuleCat.of k ((koszulChainGrading k σ M G xs i).degreeSpace q))
    (coefficientModule k σ ((koszulList k σ xs M).X i))
    (fun q => ((koszulChainGrading k σ M G xs i).degreeSpace q).subtype)
    (koszulChainGrading k σ M G xs i).degreeSum_bijective (Equiv.subRight (i:ℤ))

noncomputable def gradedKoszulSumPieceIso (i : ℕ) :
    (directSumComplex k (gradedKoszulComplex k σ M G xs)).X i ≅
      coefficientModule k σ ((koszulList k σ xs M).X i) :=
  ModuleCat.coprodIsoDirectSum (fun t : ℤ => (gradedKoszulComplex k σ M G xs t).X i) ≪≫
    (LinearEquiv.ofBijective (DirectSum.toModule k ℤ _
      (fun t => (gradedKoszulSpace k σ M G xs t i).subtype))
        (gradedKoszul_sum_bijective k σ M G xs i)).toModuleIso

@[reassoc (attr := simp)]
theorem gradedKoszulSumPieceIso_inclusion (i : ℕ) (t : ℤ) :
    colimit.ι ((familyComplex k (gradedKoszulComplex k σ M G xs)).X i) ⟨t⟩ ≫
      (gradedKoszulSumPieceIso k σ M G xs i).hom =
        (gradedKoszulInclusion k σ M G xs t).f i := by
  change Sigma.ι (fun t : ℤ => (gradedKoszulComplex k σ M G xs t).X i) t ≫
    (ModuleCat.coprodIsoDirectSum (fun t : ℤ => (gradedKoszulComplex k σ M G xs t).X i)).hom ≫ _ = _
  rw [← Category.assoc,ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  ext a
  change DirectSum.toModule k ℤ (coefficientModule k σ ((koszulList k σ xs M).X i))
    (fun t => (gradedKoszulSpace k σ M G xs t i).subtype)
      (DirectSum.lof k ℤ (fun t => gradedKoszulSpace k σ M G xs t i) t a) = a.val
  simp

/-- Splitting the actual chain complex into its internal-degree complexes. -/
noncomputable def gradedKoszulSumIso :
    directSumComplex k (gradedKoszulComplex k σ M G xs) ≅
      ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
        (koszulList k σ xs M) :=
  HomologicalComplex.Hom.isoOfComponents (gradedKoszulSumPieceIso k σ M G xs) (by
    intro i j hij
    apply colimit.hom_ext
    intro t
    rw [gradedKoszulSumPieceIso_inclusion_assoc]
    change _ = colimit.ι _ t ≫ colim.map _ ≫ _
    rw [colimit.ι_map_assoc,gradedKoszulSumPieceIso_inclusion]
    exact (gradedKoszulInclusion k σ M G xs t.as).comm i j)

/-- True graded homology decomposition, obtained from exactness of infinite coproducts. -/
noncomputable def gradedKoszulHomologySumIso (i : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
      (koszulList k σ xs M)).homology i ≅
        ModuleCat.of k (⨁ t : ℤ,(gradedKoszulComplex k σ M G xs t).homology i) :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (gradedKoszulSumIso k σ M G xs).symm ≪≫
    directSumHomologyIso k _ i

end NSP14.Homological
