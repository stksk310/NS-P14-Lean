module

import NSP14
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic

open CategoryTheory NSP14.Homological

namespace Run13IndependentAudit

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- The ordinary derived Tor, rather than a renamed Koszul definition.
theorem ordinary_residue_dimension (n i : ℕ) :
    Module.finrank (ZMod 2)
      ((ModuleCat.restrictScalars (algebraMap (ZMod 2) (VariableRing (ZMod 2) (Fin n)))).obj
        (((CategoryTheory.Tor (ModuleCat (VariableRing (ZMod 2) (Fin n))) i).obj
          (residueField (ZMod 2) (Fin n))).obj (residueField (ZMod 2) (Fin n)))) =
        Nat.choose n i := by
  rw [(torCoefficientIso (ZMod 2) (Fin n) (residueField (ZMod 2) (Fin n)) i).toLinearEquiv.finrank_eq]
  simpa [totalBetti] using residue_totalBetti (ZMod 2) (Fin n) i

example : Module.finrank (ZMod 2)
    ((ModuleCat.restrictScalars (algebraMap (ZMod 2) (VariableRing (ZMod 2) (Fin 0)))).obj
      (((CategoryTheory.Tor (ModuleCat (VariableRing (ZMod 2) (Fin 0))) 0).obj
        (residueField (ZMod 2) (Fin 0))).obj (residueField (ZMod 2) (Fin 0)))) = 1 := by
  simpa using ordinary_residue_dimension 0 0

-- Nonnegativity needs the rank-zero/exactness input: it fails for a free module.
theorem free_partial_euler_is_negative (k : Type) [Field k] :
    partialEuler (totalBetti k (Fin 2)
      (ModuleCat.of (VariableRing k (Fin 2)) (VariableRing k (Fin 2)))) 1 = -1 := by
  simp [partialEuler, totalBetti_free_zero, totalBetti_free_succ]

-- Residue-field boundaries: the last nonzero Koszul term contributes to degree two.
theorem residue_partial_euler :
    partialEuler (totalBetti (ZMod 2) (Fin 2) (residueField (ZMod 2) (Fin 2))) 1 = 1 ∧
    partialEuler (totalBetti (ZMod 2) (Fin 2) (residueField (ZMod 2) (Fin 2))) 2 = 0 := by
  simp [partialEuler, residue_totalBetti]

-- The target is independently graded actual G over a genuinely larger field.
theorem actual_degree_square (S : NSP14.NumericalSemigroup) (t : ℤ) :
    (gradedScalarKoszulIso (ZMod 2) (RatFunc (ZMod 2)) S.AtomExponent
      (S.fullGGrading (ZMod 2)) (S.fullGGrading (RatFunc (ZMod 2)))
      (S.fullG_baseChangeIso (ZMod 2) (RatFunc (ZMod 2)))
      (S.actualG_gradingScalarComparison (ZMod 2) (RatFunc (ZMod 2)))
      (variableList (ZMod 2) S.AtomExponent) t).hom ≫
        gradedKoszulInclusion (RatFunc (ZMod 2)) S.AtomExponent _
          (S.fullGGrading (RatFunc (ZMod 2))) (variableList (ZMod 2) S.AtomExponent) t =
      ((fieldExtension (ZMod 2) (RatFunc (ZMod 2))).mapHomologicalComplex _).map
        (gradedKoszulInclusion (ZMod 2) S.AtomExponent _ (S.fullGGrading (ZMod 2))
          (variableList (ZMod 2) S.AtomExponent) t) ≫
        (scalarKoszulTotalCoefficientIso (ZMod 2) (RatFunc (ZMod 2)) S.AtomExponent
          (S.fullG_baseChangeIso (ZMod 2) (RatFunc (ZMod 2)))
          (variableList (ZMod 2) S.AtomExponent)).hom :=
  gradedScalarKoszulIso_commutes _ _ _ _ _ _ _ _ _

#print axioms ordinary_residue_dimension
#print axioms free_partial_euler_is_negative
#print axioms residue_partial_euler
#print axioms actual_degree_square

end Run13IndependentAudit
