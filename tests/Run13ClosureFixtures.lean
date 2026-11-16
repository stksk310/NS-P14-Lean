module

public import NSP14
public import tests.Run13Fixtures

@[expose] public section

open CategoryTheory NSP14.Homological

namespace Run13ClosureFixtures

variable (k : Type) [Field k]

theorem square_betti : totalBetti k (Fin 1) (Run13Fixtures.squareModule k) 0=1 ∧
    totalBetti k (Fin 1) (Run13Fixtures.squareModule k) 1=1 := by
  apply principal_totalBetti k (Fin 1) ((MvPolynomial.X (0 : Fin 1))^2)
  · exact pow_ne_zero 2 (MvPolynomial.X_ne_zero _)
  · rw [variablesIdeal_all_eq_ker]
    change augmentation k (Fin 1) ((MvPolynomial.X (0 : Fin 1))^2)=0
    simp [augmentation]

theorem square_betti_above (i : ℕ) (hi : 1 < i) :
    totalBetti k (Fin 1) (Run13Fixtures.squareModule k) i=0 :=
  totalBetti_eq_zero_of_gt k (Fin 1) _ i (by simpa using hi)

theorem charTwo_square_betti :
    totalBetti (ZMod 2) (Fin 1) (Run13Fixtures.squareModule (ZMod 2)) 0=1 ∧
    totalBetti (ZMod 2) (Fin 1) (Run13Fixtures.squareModule (ZMod 2)) 1=1 := square_betti (ZMod 2)

theorem charTwo_residue_betti (i : ℕ) :
    totalBetti (ZMod 2) (Fin 3) (residueField (ZMod 2) (Fin 3)) i=Nat.choose 3 i := by
  simpa using residue_totalBetti (ZMod 2) (Fin 3) i

theorem charTwo_square_extension (i : ℕ) :
    totalBetti (RatFunc (ZMod 2)) (Fin 1)
      (polynomialBaseChangeModule (ZMod 2) (RatFunc (ZMod 2)) (Fin 1)
        (Run13Fixtures.squareModule (ZMod 2))) i=
      totalBetti (ZMod 2) (Fin 1) (Run13Fixtures.squareModule (ZMod 2)) i :=
  totalBetti_baseChange (ZMod 2) (RatFunc (ZMod 2)) (Fin 1) _ i

variable (S : NSP14.NumericalSemigroup)

theorem actualG_graded_total (i : ℕ) :
    ∃ s : Finset ℤ,(∀ t∉s,CategoryTheory.Limits.IsZero
      ((gradedKoszulComplex k S.AtomExponent _ (S.fullGGrading k) (variableList k S.AtomExponent) t).homology i)) ∧
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i=
        ∑ t∈s,gradedBetti k S.AtomExponent _ (S.fullGGrading k) i t :=
  gradedBetti_total k S.AtomExponent _ (S.fullGGrading k) i

theorem same_jump_internal_shift (s : ℕ) (hs : 0<s) (i : ℕ) (t : ℤ) :
    gradedBetti k S.NonXAtom _ (S.descendingStratumGrading k s) i t =
      gradedBetti k S.NonXAtom _ (S.ascendingStratumGrading k s hs) i (t+(s:ℤ)) :=
  S.jumpStratum_gradedBetti k s hs i t

end Run13ClosureFixtures
