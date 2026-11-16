module

public import NSP14.Homological.KoszulGradedMaps
public import NSP14.Homological.ActualCoefficientBaseChange
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L] [Fintype σ]
variable (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M)

/-- Scalar extension of the actual internal-degree complex, retaining its degree label. -/
noncomputable def extendedGradedKoszulComplex (t : ℤ) : ChainComplex (ModuleCat.{u} L) ℕ :=
  ((fieldExtension k L).mapHomologicalComplex _).obj
    (gradedKoszulComplex k σ M G (variableList k σ) t)

/-- The actual extended degree complex maps into the Koszul complex of the actual L[X]-module. -/
noncomputable def extendedGradedKoszulInclusion (t : ℤ) :
    extendedGradedKoszulComplex k L σ M G t ⟶
      coefficientKoszulComplex L σ (polynomialBaseChangeModule k L σ M) :=
  ((fieldExtension k L).mapHomologicalComplex _).map
    (gradedKoszulInclusion k σ M G (variableList k σ) t) ≫
      (koszulPolynomialCoefficientBaseChangeIso k L σ M).hom

noncomputable def extendedGradedHomologyIso (i : ℕ) (t : ℤ) :
    (extendedGradedKoszulComplex k L σ M G t).homology i ≅
      (fieldExtension k L).obj ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
  fieldExtensionHomologyIso k L _ i

/-- These are degree summands of the actual changed-polynomial Koszul homology,
not arbitrary vector spaces with matching dimensions. -/
noncomputable def extendedGradedHomologySumIso (i : ℕ) :
    (coefficientKoszulComplex L σ (polynomialBaseChangeModule k L σ M)).homology i ≅
      ModuleCat.of L (⨁ t : ℤ,(extendedGradedKoszulComplex k L σ M G t).homology i) := by
  classical
  let A := fun t : ℤ => (gradedKoszulComplex k σ M G (variableList k σ) t).homology i
  exact (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
      (koszulPolynomialCoefficientBaseChangeIso k L σ M).symm ≪≫
    fieldExtensionHomologyIso k L _ i ≪≫
    (fieldExtension k L).mapIso (gradedKoszulHomologySumIso k σ M G (variableList k σ) i) ≪≫
    (TensorProduct.directSumRight k L L (fun t : ℤ => A t)).toModuleIso ≪≫
    (DirectSum.congrLinearEquiv (fun t => (extendedGradedHomologyIso k L σ M G i t).symm.toLinearEquiv)).toModuleIso

noncomputable def extendedGradedBetti (i : ℕ) (t : ℤ) : ℕ :=
  Module.finrank L ((extendedGradedKoszulComplex k L σ M G t).homology i)

/-- Same-characteristic extension preserves each inherited graded Betti number. -/
theorem gradedBetti_baseChange [Module.Finite (VariableRing k σ) M] (i : ℕ) (t : ℤ) :
    extendedGradedBetti k L σ M G i t=gradedBetti k σ M G i t :=
  (extendedGradedHomologyIso k L σ M G i t).toLinearEquiv.finrank_eq.trans (fieldExtension_finrank k L _)

end NSP14.Homological
