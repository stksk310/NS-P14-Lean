module

public import NSP14.Homological.CoordinateScalarComparison
public import NSP14.Homological.GradedScalarKoszul
public import NSP14.Homological.ActualCoefficientBaseChange

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory NSP14.Homological
open scoped TensorProduct

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k L : Type) [Field k] [Field L] [Algebra k L]

/-- The existing actual coefficient-change map respects the independently defined order pieces. -/
noncomputable def actualG_gradingScalarComparison :
    GradedScalarComparison k L (S.AtomExponent) (S.fullGGrading k) (S.fullGGrading L) (S.fullG_baseChangeIso k L) :=
  coordinateGradedScalarComparison k L (S.AtomExponent) (S.carrier)
    (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) (ModuleCat.of (S.FullPolynomialRing L) (S.TangentAlgebra L))
    ((coefficientOriginalEquiv k (S.AtomExponent) (S.TangentAlgebra k)).trans (S.tangentCoordinates k))
    ((coefficientOriginalEquiv L (S.AtomExponent) (S.TangentAlgebra L)).trans (S.tangentCoordinates L))
    (fun t => ((S.order t.val : ℕ) : ℤ)) (S.fullGGrading k) (S.fullGGrading L) (S.fullG_baseChangeIso k L)
    (fun _ => LinearEquiv.refl k _) (fun _ => LinearEquiv.refl L _)
    (by intro q a; rfl) (by intro q a; rfl) (by
      intro a i
      dsimp only [fullG_baseChangeIso]
      erw [coordinateBaseChangePolynomialIso_tmul]
      rw [mul_one])

/-- Extension of each actual degree complex identifies with actual G over L at the same degree. -/
noncomputable def actualG_gradedKoszulBaseChangeIso (t : ℤ) :
    extendedGradedKoszulComplex k L (S.AtomExponent) _ (S.fullGGrading k) t ≅
      gradedKoszulComplex L (S.AtomExponent) _ (S.fullGGrading L) (variableList L (S.AtomExponent)) t :=
  gradedScalarKoszulIso k L (S.AtomExponent) (S.fullGGrading k) (S.fullGGrading L) (S.fullG_baseChangeIso k L)
    (S.actualG_gradingScalarComparison k L) (variableList k (S.AtomExponent)) t

theorem actualG_gradedBetti_baseChange (i : ℕ) (t : ℤ) :
    gradedBetti L (S.AtomExponent) _ (S.fullGGrading L) i t = gradedBetti k (S.AtomExponent) _ (S.fullGGrading k) i t :=
  gradedScalarBetti_baseChange k L (S.AtomExponent) (S.fullGGrading k) (S.fullGGrading L)
    (S.fullG_baseChangeIso k L) (S.actualG_gradingScalarComparison k L) i t

/-- The existing actual coefficient-change map respects the independently defined order pieces. -/
noncomputable def actualT_gradingScalarComparison :
    GradedScalarComparison k L (S.NonXAtom) (S.actualTGrading k) (S.actualTGrading L) (S.actualT_baseChangeIso k L) :=
  coordinateGradedScalarComparison k L (S.NonXAtom) (S.TerminalExponent)
    (ModuleCat.of (S.PolynomialRing k) ((S.xMultiply k).ker)) (ModuleCat.of (S.PolynomialRing L) ((S.xMultiply L).ker))
    ((coefficientOriginalEquiv k (S.NonXAtom) ((S.xMultiply k).ker)).trans (S.xKernelEquiv k))
    ((coefficientOriginalEquiv L (S.NonXAtom) ((S.xMultiply L).ker)).trans (S.xKernelEquiv L))
    (fun t => ((S.order t.val.val : ℕ) : ℤ)) (S.actualTGrading k) (S.actualTGrading L) (S.actualT_baseChangeIso k L)
    (fun _ => LinearEquiv.refl k _) (fun _ => LinearEquiv.refl L _)
    (by intro q a; rfl) (by intro q a; rfl) (by
      intro a i
      dsimp only [actualT_baseChangeIso]
      erw [coordinateBaseChangePolynomialIso_tmul]
      rw [mul_one])

/-- Extension of each actual degree complex identifies with actual T over L at the same degree. -/
noncomputable def actualT_gradedKoszulBaseChangeIso (t : ℤ) :
    extendedGradedKoszulComplex k L (S.NonXAtom) _ (S.actualTGrading k) t ≅
      gradedKoszulComplex L (S.NonXAtom) _ (S.actualTGrading L) (variableList L (S.NonXAtom)) t :=
  gradedScalarKoszulIso k L (S.NonXAtom) (S.actualTGrading k) (S.actualTGrading L) (S.actualT_baseChangeIso k L)
    (S.actualT_gradingScalarComparison k L) (variableList k (S.NonXAtom)) t

theorem actualT_gradedBetti_baseChange (i : ℕ) (t : ℤ) :
    gradedBetti L (S.NonXAtom) _ (S.actualTGrading L) i t = gradedBetti k (S.NonXAtom) _ (S.actualTGrading k) i t :=
  gradedScalarBetti_baseChange k L (S.NonXAtom) (S.actualTGrading k) (S.actualTGrading L)
    (S.actualT_baseChangeIso k L) (S.actualT_gradingScalarComparison k L) i t

/-- The existing actual coefficient-change map respects the independently defined order pieces. -/
noncomputable def actualA_gradingScalarComparison :
    GradedScalarComparison k L (S.NonXAtom) (S.actualAGrading k) (S.actualAGrading L) (S.actualA_baseChangeIso k L) :=
  coordinateGradedScalarComparison k L (S.NonXAtom) (S.HeadExponent)
    (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)) (ModuleCat.of (S.PolynomialRing L) (S.HeadAlgebra L))
    ((coefficientOriginalEquiv k (S.NonXAtom) (S.HeadAlgebra k)).trans (S.headQuotientEquiv k))
    ((coefficientOriginalEquiv L (S.NonXAtom) (S.HeadAlgebra L)).trans (S.headQuotientEquiv L))
    (fun t => ((S.order t.val.val : ℕ) : ℤ)) (S.actualAGrading k) (S.actualAGrading L) (S.actualA_baseChangeIso k L)
    (fun _ => LinearEquiv.refl k _) (fun _ => LinearEquiv.refl L _)
    (by intro q a; rfl) (by intro q a; rfl) (by
      intro a i
      dsimp only [actualA_baseChangeIso]
      erw [coordinateBaseChangePolynomialIso_tmul]
      rw [mul_one])

/-- Extension of each actual degree complex identifies with actual A over L at the same degree. -/
noncomputable def actualA_gradedKoszulBaseChangeIso (t : ℤ) :
    extendedGradedKoszulComplex k L (S.NonXAtom) _ (S.actualAGrading k) t ≅
      gradedKoszulComplex L (S.NonXAtom) _ (S.actualAGrading L) (variableList L (S.NonXAtom)) t :=
  gradedScalarKoszulIso k L (S.NonXAtom) (S.actualAGrading k) (S.actualAGrading L) (S.actualA_baseChangeIso k L)
    (S.actualA_gradingScalarComparison k L) (variableList k (S.NonXAtom)) t

theorem actualA_gradedBetti_baseChange (i : ℕ) (t : ℤ) :
    gradedBetti L (S.NonXAtom) _ (S.actualAGrading L) i t = gradedBetti k (S.NonXAtom) _ (S.actualAGrading k) i t :=
  gradedScalarBetti_baseChange k L (S.NonXAtom) (S.actualAGrading k) (S.actualAGrading L)
    (S.actualA_baseChangeIso k L) (S.actualA_gradingScalarComparison k L) i t

/-- The existing actual coefficient-change map respects the independently defined order pieces. -/
noncomputable def actualN_gradingScalarComparison :
    GradedScalarComparison k L (S.NonXAtom) (S.actualNGrading k) (S.actualNGrading L) (S.actualN_baseChangeIso k L) :=
  coordinateGradedScalarComparison k L (S.NonXAtom) (S.NonAperyHeadExponent)
    (ModuleCat.of (S.PolynomialRing k) (((S.nonAperyIdeal k).restrictScalars k))) (ModuleCat.of (S.PolynomialRing L) (((S.nonAperyIdeal L).restrictScalars L)))
    ((coefficientOriginalEquiv k (S.NonXAtom) (((S.nonAperyIdeal k).restrictScalars k))).trans (S.nonAperyIdealEquiv k))
    ((coefficientOriginalEquiv L (S.NonXAtom) (((S.nonAperyIdeal L).restrictScalars L))).trans (S.nonAperyIdealEquiv L))
    (fun t => ((S.order t.val.val.val : ℕ) : ℤ)) (S.actualNGrading k) (S.actualNGrading L) (S.actualN_baseChangeIso k L)
    (fun _ => LinearEquiv.refl k _) (fun _ => LinearEquiv.refl L _)
    (by intro q a; rfl) (by intro q a; rfl) (by
      intro a i
      dsimp only [actualN_baseChangeIso]
      erw [coordinateBaseChangePolynomialIso_tmul]
      rw [mul_one])

/-- Extension of each actual degree complex identifies with actual N over L at the same degree. -/
noncomputable def actualN_gradedKoszulBaseChangeIso (t : ℤ) :
    extendedGradedKoszulComplex k L (S.NonXAtom) _ (S.actualNGrading k) t ≅
      gradedKoszulComplex L (S.NonXAtom) _ (S.actualNGrading L) (variableList L (S.NonXAtom)) t :=
  gradedScalarKoszulIso k L (S.NonXAtom) (S.actualNGrading k) (S.actualNGrading L) (S.actualN_baseChangeIso k L)
    (S.actualN_gradingScalarComparison k L) (variableList k (S.NonXAtom)) t

theorem actualN_gradedBetti_baseChange (i : ℕ) (t : ℤ) :
    gradedBetti L (S.NonXAtom) _ (S.actualNGrading L) i t = gradedBetti k (S.NonXAtom) _ (S.actualNGrading k) i t :=
  gradedScalarBetti_baseChange k L (S.NonXAtom) (S.actualNGrading k) (S.actualNGrading L)
    (S.actualN_baseChangeIso k L) (S.actualN_gradingScalarComparison k L) i t

/-- The existing actual coefficient-change map respects the independently defined order pieces. -/
noncomputable def actualQ_gradingScalarComparison :
    GradedScalarComparison k L (S.NonXAtom) (S.actualQGrading k) (S.actualQGrading L) (S.actualQ_baseChangeIso k L) :=
  coordinateGradedScalarComparison k L (S.NonXAtom) (S.AperyExponent)
    (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k)) (ModuleCat.of (S.PolynomialRing L) (S.AperyAlgebra L))
    ((coefficientOriginalEquiv k (S.NonXAtom) (S.AperyAlgebra k)).trans (S.aperyQuotientEquiv k))
    ((coefficientOriginalEquiv L (S.NonXAtom) (S.AperyAlgebra L)).trans (S.aperyQuotientEquiv L))
    (fun t => ((S.order t.val.val : ℕ) : ℤ)) (S.actualQGrading k) (S.actualQGrading L) (S.actualQ_baseChangeIso k L)
    (fun _ => LinearEquiv.refl k _) (fun _ => LinearEquiv.refl L _)
    (by intro q a; rfl) (by intro q a; rfl) (by
      intro a i
      dsimp only [actualQ_baseChangeIso]
      erw [coordinateBaseChangePolynomialIso_tmul]
      rw [mul_one])

/-- Extension of each actual degree complex identifies with actual Q over L at the same degree. -/
noncomputable def actualQ_gradedKoszulBaseChangeIso (t : ℤ) :
    extendedGradedKoszulComplex k L (S.NonXAtom) _ (S.actualQGrading k) t ≅
      gradedKoszulComplex L (S.NonXAtom) _ (S.actualQGrading L) (variableList L (S.NonXAtom)) t :=
  gradedScalarKoszulIso k L (S.NonXAtom) (S.actualQGrading k) (S.actualQGrading L) (S.actualQ_baseChangeIso k L)
    (S.actualQ_gradingScalarComparison k L) (variableList k (S.NonXAtom)) t

theorem actualQ_gradedBetti_baseChange (i : ℕ) (t : ℤ) :
    gradedBetti L (S.NonXAtom) _ (S.actualQGrading L) i t = gradedBetti k (S.NonXAtom) _ (S.actualQGrading k) i t :=
  gradedScalarBetti_baseChange k L (S.NonXAtom) (S.actualQGrading k) (S.actualQGrading L)
    (S.actualQ_baseChangeIso k L) (S.actualQ_gradingScalarComparison k L) i t

end NSP14.NumericalSemigroup
