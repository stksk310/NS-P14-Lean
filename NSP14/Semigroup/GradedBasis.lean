module

public import NSP14.Semigroup.GradedPieces
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- A coarse conductor bound suffices to prove every homogeneous exponent set finite. -/
theorem order_level_bound (x n : ℕ) (hn : S.order x ≤ n) :
    x < (n + 1) * (S.conductor + 1) := by
  by_contra h
  have hbig : (n + 1) * (S.conductor + 1) ≤ x := by omega
  have hnx : n * (S.conductor + 1) ≤ x := by nlinarith
  have hprod : (n + 1) * (S.conductor + 1) =
      n * (S.conductor + 1) + (S.conductor + 1) := by ring
  rw [hprod] at hbig
  have hrem : S.conductor + 1 ≤ x - n * (S.conductor + 1) := by omega
  have hmem : x - n * (S.conductor + 1) ∈ S := S.cofinite _ (by omega)
  have hconst : S.HasLength (n * (S.conductor + 1)) n :=
    ⟨fun _ => S.conductor + 1, fun _ => ⟨S.cofinite _ (by change S.conductor ≤ S.conductor + 1; omega),
      by change 0 < S.conductor + 1; omega⟩, by simp⟩
  have hlen := S.length_add (S.length_one hmem (by omega)) hconst
  rw [Nat.sub_add_cancel hnx] at hlen
  have ho := S.length_le_order hlen
  omega

instance degreeExponentFinite (n : ℕ) : Finite (S.DegreeExponent n) := by
  let f : S.DegreeExponent n → Fin ((n + 1) * (S.conductor + 1)) :=
    fun x => ⟨x.val.val, S.order_level_bound x.val.val n (le_of_eq x.property)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Fin.val h

variable (k : Type*) [CommRing k]

/-- The actual homogeneous quotient has the order=n monomials as a basis. -/
noncomputable def gradedPieceBasis (n : ℕ) :
    Module.Basis (S.DegreeExponent n) k (S.GradedPiece k n) :=
  Finsupp.basisSingleOne.map (S.gradedPieceEquiv k n).symm

theorem gradedPieceBasis_coordinates (n : ℕ) (x : S.DegreeExponent n) :
    S.gradedPieceEquiv k n (S.gradedPieceBasis k n x) = Finsupp.single x 1 := by
  simp [gradedPieceBasis]

/-- Basis vectors really are the initial monomial classes. -/
theorem gradedPieceBasis_eq_monomial (n : ℕ) (x : S.DegreeExponent n) :
    S.gradedPieceBasis k n x =
      S.monomialClass k n x.val (le_of_eq x.property.symm) := by
  classical
  apply (S.gradedPieceEquiv k n).injective
  rw [S.gradedPieceBasis_coordinates]
  rw [monomialClass, S.gradedPieceEquiv_mk]
  ext y
  change Finsupp.single x (1 : k) y = Finsupp.single x.val (1 : k) y.val
  by_cases h : x = y
  · subst y; simp
  · have hv : x.val ≠ y.val := fun heq => h (Subtype.ext heq)
    simp [h, hv]

end NSP14.NumericalSemigroup
