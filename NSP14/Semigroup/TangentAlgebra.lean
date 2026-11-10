module

public import NSP14.Semigroup.GradedProduct
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

open scoped DirectSum

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- Explicit family instance for higher-order graded typeclass inference. -/
noncomputable instance pieceAddCommGroup (n : ℕ) : AddCommGroup (S.GradedPiece k n) :=
  inferInstanceAs (AddCommGroup ((S.powerModule k n) ⧸ S.nextPower k n))

/-- A constant representative in the actual zeroth ideal power. -/
noncomputable def zeroRepresentative (c : S.SemigroupRing k) : S.powerModule k 0 :=
  ⟨c, by change c ∈ S.positiveIdeal k ^ 0; simp⟩

/-- Equality of homogeneous classes, retaining their degree indices. -/
theorem homogeneous_mk_eq {n p : ℕ} (h : n = p)
    (f : S.powerModule k n) (g : S.powerModule k p) (heq : f.val = g.val) :
    GradedMonoid.mk (A := S.GradedPiece k) n (Submodule.Quotient.mk f : S.GradedPiece k n) =
      GradedMonoid.mk (A := S.GradedPiece k) p (Submodule.Quotient.mk g : S.GradedPiece k p) := by
  subst p
  have : f = g := Subtype.ext heq
  subst g
  rfl

noncomputable instance pieceGOne : GradedMonoid.GOne (S.GradedPiece k) :=
  ⟨Submodule.Quotient.mk (S.zeroRepresentative k 1)⟩

noncomputable instance pieceGMul : GradedMonoid.GMul (S.GradedPiece k) :=
  ⟨fun a b => S.gradedMul k _ _ a b⟩

noncomputable instance pieceGCommRing : DirectSum.GCommRing (S.GradedPiece k) where
  mul := fun {n p} a b => S.gradedMul k n p a b
  one := Submodule.Quotient.mk (S.zeroRepresentative k 1)
  mul_zero := by intro n p a; exact map_zero (S.gradedMul k n p a)
  zero_mul := by
    intro n p b
    exact LinearMap.congr_fun (map_zero (S.gradedMul k n p)) b
  mul_add := by intro n p a b c; exact map_add (S.gradedMul k n p a) b c
  add_mul := by intro n p a b c; exact LinearMap.congr_fun (map_add (S.gradedMul k n p) a b) c
  one_mul := by
    rintro ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (0 + n) (S.gradedMul k 0 n
        (Submodule.Quotient.mk _) (Submodule.Quotient.mk f)) = _
      rw [S.gradedMul_mk]
      exact S.homogeneous_mk_eq k (Nat.zero_add n) _ f (one_mul _)
  mul_one := by
    rintro ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (n + 0) (S.gradedMul k n 0
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk _)) = _
      rw [S.gradedMul_mk]
      exact S.homogeneous_mk_eq k (Nat.add_zero n) _ f (mul_one _)
  mul_assoc := by
    rintro ⟨n, a⟩ ⟨p, b⟩ ⟨q, c⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      induction b using Submodule.Quotient.induction_on with
      | _ g =>
        induction c using Submodule.Quotient.induction_on with
        | _ h =>
          change GradedMonoid.mk ((n + p) + q)
            (S.gradedMul k (n + p) q (S.gradedMul k n p
              (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)) (Submodule.Quotient.mk h)) =
            GradedMonoid.mk (n + (p + q))
            (S.gradedMul k n (p + q) (Submodule.Quotient.mk f) (S.gradedMul k p q
              (Submodule.Quotient.mk g) (Submodule.Quotient.mk h)))
          simp only [S.gradedMul_mk]
          exact S.homogeneous_mk_eq k (Nat.add_assoc n p q) _ _ (mul_assoc _ _ _)
  mul_comm := by
    rintro ⟨n, a⟩ ⟨p, b⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      induction b using Submodule.Quotient.induction_on with
      | _ g =>
        change GradedMonoid.mk (n + p) (S.gradedMul k n p
          (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)) =
          GradedMonoid.mk (p + n) (S.gradedMul k p n
          (Submodule.Quotient.mk g) (Submodule.Quotient.mk f))
        simp only [S.gradedMul_mk]
        exact S.homogeneous_mk_eq k (Nat.add_comm n p) _ _ (mul_comm _ _)
  natCast := fun n => Submodule.Quotient.mk (S.zeroRepresentative k n)
  natCast_zero := by
    simp only [Nat.cast_zero]
    rfl
  natCast_succ := by
    intro n
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact Nat.cast_add_one _
  intCast := fun n => Submodule.Quotient.mk (S.zeroRepresentative k n)
  intCast_ofNat := by intro n; simp only [Int.cast_natCast]
  intCast_negSucc_ofNat := by
    intro n
    rw [← Submodule.Quotient.mk_neg]
    congr 1
    apply Subtype.ext
    exact Int.cast_negSucc _

/-- The associated graded ring of the positive ideal of algebraic k[S]. -/
abbrev TangentAlgebra := ⨁ n : ℕ, S.GradedPiece k n

noncomputable instance tangentCommRing : CommRing (S.TangentAlgebra k) :=
  DirectSum.commRing (S.GradedPiece k)

theorem tangent_of_mul (n p : ℕ) (a : S.GradedPiece k n) (b : S.GradedPiece k p) :
    DirectSum.of (S.GradedPiece k) n a * DirectSum.of (S.GradedPiece k) p b =
      DirectSum.of (S.GradedPiece k) (n + p) (S.gradedMul k n p a b) :=
  DirectSum.of_mul_of a b

end NSP14.NumericalSemigroup
