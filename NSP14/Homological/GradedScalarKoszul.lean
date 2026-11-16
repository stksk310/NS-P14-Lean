module

public import NSP14.Homological.ScalarKoszulInclusions
public import NSP14.Homological.ComplexRestriction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]
variable {M : ModuleCat.{u} (VariableRing k σ)} {N : ModuleCat.{u} (VariableRing L σ)}
variable (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N)
variable (e : polynomialBaseChangeModule k L σ M ≅ N)

/-- The actual total coefficient-complex comparison associated to the specified module map e. -/
noncomputable def scalarKoszulTotalCoefficientIso (xs : List σ) :
    ((fieldExtension k L).mapHomologicalComplex _).obj
      (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
        (koszulList k σ xs M)) ≅
    ((ModuleCat.restrictScalars (algebraMap L (VariableRing L σ))).mapHomologicalComplex _).obj
      (koszulList L σ xs N) :=
  (coefficientChainBaseChangeIso k L σ (koszulList k σ xs M)).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap L (VariableRing L σ))).mapHomologicalComplex _).mapIso
      (polynomialKoszulTotalIso k L σ e xs)

noncomputable def scalarKoszulGradeSpaceIso (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (t : ℤ) (i : ℕ) :
    (L ⊗[k] gradedKoszulSpace k σ M G xs t i) ≃ₗ[L] gradedKoszulSpace L σ N H xs t i :=
  (LinearEquiv.baseChange k L _ _
    ((koszulChainGrading k σ M G xs i).rangeEquiv (t-(i:ℤ))).symm).trans
      ((scalarKoszulGradePieceIso k L σ G H e C xs i (t-(i:ℤ))).trans
        ((koszulChainGrading L σ N H xs i).rangeEquiv (t-(i:ℤ))))

theorem scalarKoszulGradeSpaceIso_one_tmul (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (t : ℤ) (i : ℕ) (a : gradedKoszulSpace k σ M G xs t i) :
    (scalarKoszulGradeSpaceIso k L σ G H e C xs t i ((1:L) ⊗ₜ[k] a)).val =
      scalarKoszulPieceIso k L σ e xs i ((1:L) ⊗ₜ[k] a.val) := by
  simp only [scalarKoszulGradeSpaceIso,LinearEquiv.trans_apply]
  change (koszulChainGrading L σ N H xs i).inclusion (t-(i:ℤ))
    (scalarKoszulGradePieceIso k L σ G H e C xs i (t-(i:ℤ))
      ((1:L) ⊗ₜ[k] ((koszulChainGrading k σ M G xs i).rangeEquiv (t-(i:ℤ))).symm a)) = _
  rw [scalarKoszulGradePieceIso_inclusion]
  have ha := congrArg Subtype.val
    (((koszulChainGrading k σ M G xs i).rangeEquiv (t-(i:ℤ))).apply_symm_apply a)
  change (koszulChainGrading k σ M G xs i).inclusion (t-(i:ℤ))
    (((koszulChainGrading k σ M G xs i).rangeEquiv (t-(i:ℤ))).symm a)=a.val at ha
  rw [ha]

/-- Compatibility with the total comparison on every tensor, not only homogeneous basis vectors. -/
theorem scalarKoszulGradeSpaceIso_inclusion (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (t : ℤ) (i : ℕ) (a : L ⊗[k] gradedKoszulSpace k σ M G xs t i) :
    (scalarKoszulGradeSpaceIso k L σ G H e C xs t i a).val =
      scalarKoszulPieceIso k L σ e xs i
        (((gradedKoszulSpace k σ M G xs t i).subtype).baseChange L a) := by
  induction a using TensorProduct.inductionOn with
  | tmul l a =>
    simp only [LinearMap.baseChange_tmul]
    have ht : l ⊗ₜ[k] a = l • ((1:L) ⊗ₜ[k] a) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [ht,map_smul]
    simp only [Submodule.coe_smul]
    rw [scalarKoszulGradeSpaceIso_one_tmul,← map_smul]
    congr 1
    simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rfl
  | add a b ha hb =>
    simp only [map_add,Submodule.coe_add,ha,hb]

/-- Extend the actual internal degree complex and identify it with the separately specified
actual target grading. The isomorphism commutes with the same total coefficient change. -/
noncomputable def gradedScalarKoszulIso (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (t : ℤ) :
    ((fieldExtension k L).mapHomologicalComplex _).obj (gradedKoszulComplex k σ M G xs t) ≅
      gradedKoszulComplex L σ N H xs t := by
  let A := ((fieldExtension k L).mapHomologicalComplex _).map (gradedKoszulInclusion k σ M G xs t)
  let B := gradedKoszulInclusion L σ N H xs t
  let E := scalarKoszulTotalCoefficientIso k L σ e xs
  let f := fun i => (scalarKoszulGradeSpaceIso k L σ G H e C xs t i).toModuleIso
  let : ∀ i,Mono (B.f i) := fun i => (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  apply complexIsoOfRestrictions E A B f
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact scalarKoszulGradeSpaceIso_inclusion k L σ G H e C xs t i a

/-- The degree-complex isomorphism commutes with the original total comparison and actual inclusions. -/
theorem gradedScalarKoszulIso_commutes (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (t : ℤ) :
    (gradedScalarKoszulIso k L σ G H e C xs t).hom ≫ gradedKoszulInclusion L σ N H xs t =
      ((fieldExtension k L).mapHomologicalComplex _).map (gradedKoszulInclusion k σ M G xs t) ≫
        (scalarKoszulTotalCoefficientIso k L σ e xs).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact scalarKoszulGradeSpaceIso_inclusion k L σ G H e C xs t i a

/-- Graded Betti invariance for the specified, independently graded actual target. -/
theorem gradedScalarBetti_baseChange [Fintype σ]
    [Module.Finite (VariableRing k σ) M] [Module.Finite (VariableRing L σ) N]
    (C : GradedScalarComparison k L σ G H e) (i : ℕ) (t : ℤ) :
    gradedBetti L σ N H i t=gradedBetti k σ M G i t :=
  ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
    (gradedScalarKoszulIso k L σ G H e C (variableList k σ) t)).toLinearEquiv.finrank_eq.symm.trans
      (gradedBetti_baseChange k L σ M G i t)

end NSP14.Homological
