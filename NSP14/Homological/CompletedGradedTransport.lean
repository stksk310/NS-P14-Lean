module

public import NSP14.Homological.ActualGradedTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

/-- Run12's graded completed-cone comparison equips its actual full-P module with the
transported ideal-power grading. It is the same polynomial-linear comparison as before. -/
noncomputable def completedFullGGrading : GradedPolynomialModule k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) :=
  (S.fullGGrading k).transport (S.completedPolynomialLinearEquiv k).toModuleIso

noncomputable def completedGradedKoszulIso (t : ℤ) :
    gradedKoszulComplex k S.AtomExponent _ (S.fullGGrading k) (variableList k S.AtomExponent) t ≅
      gradedKoszulComplex k S.AtomExponent _ (S.completedFullGGrading k) (variableList k S.AtomExponent) t :=
  gradedKoszulIso k S.AtomExponent (S.fullGGrading k) (S.completedFullGGrading k)
    (S.completedPolynomialLinearEquiv k).toModuleIso 0 (by
      intro q a
      rw [add_zero,completedFullGGrading,GradedPolynomialModule.transport_mem]
      simp) (variableList k S.AtomExponent) t ≪≫ eqToIso (by rw [add_zero])

theorem completed_gradedBetti (i : ℕ) (t : ℤ) :
    gradedBetti k S.AtomExponent _ (S.fullGGrading k) i t =
      gradedBetti k S.AtomExponent _ (S.completedFullGGrading k) i t :=
  ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
    (S.completedGradedKoszulIso k t)).toLinearEquiv.finrank_eq

end NSP14.NumericalSemigroup
