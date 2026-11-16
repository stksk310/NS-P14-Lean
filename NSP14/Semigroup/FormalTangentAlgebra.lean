module

public import NSP14.Semigroup.FormalFactorization
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.DirectSum.Algebra

@[expose] public section

open scoped DirectSum

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable def formalPowerModule (n : ℕ) : Submodule k (S.FormalSemigroupRing k) :=
  (S.formalMaximalIdeal k ^ n).restrictScalars k

noncomputable def formalNextPower (n : ℕ) : Submodule k (S.formalPowerModule k n) :=
  (S.formalPowerModule k (n+1)).comap (S.formalPowerModule k n).subtype

/-- The quotient of actual powers in the literal formal semigroup ring. -/
abbrev FormalGradedPiece (n : ℕ) := (S.formalPowerModule k n) ⧸ (S.formalNextPower k n)

/-- Multiplication of representatives, followed by the homogeneous quotient map. -/
noncomputable def formalRepresentativeProduct (n p : ℕ) :
    S.formalPowerModule k n →ₗ[k] S.formalPowerModule k p →ₗ[k] S.FormalGradedPiece k (n + p) where
  toFun f :=
    { toFun := fun g => Submodule.Quotient.mk ⟨f.val * g.val,
        by
          change f.val * g.val ∈ S.formalMaximalIdeal k ^ (n + p)
          rw [pow_add]
          exact Ideal.mul_mem_mul f.property g.property⟩
      map_add' := by intros; simp [mul_add]; rfl
      map_smul' := by intros; simp; rfl }
  map_add' := by intros; ext; simp [add_mul]; rfl
  map_smul' := by intros; ext; simp; rfl

theorem formalRepresentativeProduct_left_zero (n p : ℕ) :
    S.formalNextPower k n ≤ (S.formalRepresentativeProduct k n p).ker := by
  intro f hf
  ext g
  rw [LinearMap.zero_apply]
  change (Submodule.Quotient.mk _ : S.FormalGradedPiece k (n + p)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change f.val * g.val ∈ S.formalMaximalIdeal k ^ (n + p + 1)
  have hf' : f.val ∈ S.formalMaximalIdeal k ^ (n + 1) := hf
  have hm := Ideal.mul_mem_mul hf' g.property
  simpa [← pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem formalRepresentativeProduct_right_zero (n p : ℕ) :
    S.formalNextPower k p ≤ (S.formalRepresentativeProduct k n p).flip.ker := by
  intro g hg
  ext f
  rw [LinearMap.zero_apply]
  change (Submodule.Quotient.mk _ : S.FormalGradedPiece k (n + p)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change f.val * g.val ∈ S.formalMaximalIdeal k ^ (n + p + 1)
  have hg' : g.val ∈ S.formalMaximalIdeal k ^ (p + 1) := hg
  have hm := Ideal.mul_mem_mul f.property hg'
  simpa [← pow_add, Nat.add_assoc] using hm

/-- Well-defined multiplication of homogeneous pieces of the actual associated graded. -/
noncomputable def formalGradedMul (n p : ℕ) :
    S.FormalGradedPiece k n →ₗ[k] S.FormalGradedPiece k p →ₗ[k] S.FormalGradedPiece k (n + p) :=
  (S.formalRepresentativeProduct k n p).liftQ₂ (S.formalNextPower k n) (S.formalNextPower k p)
    (S.formalRepresentativeProduct_left_zero k n p) (S.formalRepresentativeProduct_right_zero k n p)

theorem formalGradedMul_mk (n p : ℕ) (f : S.formalPowerModule k n) (g : S.formalPowerModule k p) :
    S.formalGradedMul k n p (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk ⟨f.val * g.val,
        by
          change f.val * g.val ∈ S.formalMaximalIdeal k ^ (n + p)
          rw [pow_add]
          exact Ideal.mul_mem_mul f.property g.property⟩ := rfl

/-- Explicit family instance for higher-order graded typeclass inference. -/
noncomputable instance formalPieceAddCommGroup (n : ℕ) : AddCommGroup (S.FormalGradedPiece k n) :=
  inferInstanceAs (AddCommGroup ((S.formalPowerModule k n) ⧸ S.formalNextPower k n))

/-- A constant representative in the actual zeroth ideal power. -/
noncomputable def formalZeroRepresentative (c : S.FormalSemigroupRing k) : S.formalPowerModule k 0 :=
  ⟨c, by change c ∈ S.formalMaximalIdeal k ^ 0; simp⟩

/-- Equality of homogeneous classes, retaining their degree indices. -/
theorem formal_homogeneous_mk_eq {n p : ℕ} (h : n = p)
    (f : S.formalPowerModule k n) (g : S.formalPowerModule k p) (heq : f.val = g.val) :
    GradedMonoid.mk (A := S.FormalGradedPiece k) n (Submodule.Quotient.mk f : S.FormalGradedPiece k n) =
      GradedMonoid.mk (A := S.FormalGradedPiece k) p (Submodule.Quotient.mk g : S.FormalGradedPiece k p) := by
  subst p
  have : f = g := Subtype.ext heq
  subst g
  rfl

noncomputable instance formalPieceGOne : GradedMonoid.GOne (S.FormalGradedPiece k) :=
  ⟨Submodule.Quotient.mk (S.formalZeroRepresentative k 1)⟩

noncomputable instance formalPieceGMul : GradedMonoid.GMul (S.FormalGradedPiece k) :=
  ⟨fun a b => S.formalGradedMul k _ _ a b⟩

noncomputable instance formalPieceGCommRing : DirectSum.GCommRing (S.FormalGradedPiece k) where
  mul := fun {n p} a b => S.formalGradedMul k n p a b
  one := Submodule.Quotient.mk (S.formalZeroRepresentative k 1)
  mul_zero := by intro n p a; exact map_zero (S.formalGradedMul k n p a)
  zero_mul := by
    intro n p b
    exact LinearMap.congr_fun (map_zero (S.formalGradedMul k n p)) b
  mul_add := by intro n p a b c; exact map_add (S.formalGradedMul k n p a) b c
  add_mul := by intro n p a b c; exact LinearMap.congr_fun (map_add (S.formalGradedMul k n p) a b) c
  one_mul := by
    rintro ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (0 + n) (S.formalGradedMul k 0 n
        (Submodule.Quotient.mk _) (Submodule.Quotient.mk f)) = _
      rw [S.formalGradedMul_mk]
      exact S.formal_homogeneous_mk_eq k (Nat.zero_add n) _ f (one_mul _)
  mul_one := by
    rintro ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (n + 0) (S.formalGradedMul k n 0
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk _)) = _
      rw [S.formalGradedMul_mk]
      exact S.formal_homogeneous_mk_eq k (Nat.add_zero n) _ f (mul_one _)
  mul_assoc := by
    rintro ⟨n, a⟩ ⟨p, b⟩ ⟨q, c⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      induction b using Submodule.Quotient.induction_on with
      | _ g =>
        induction c using Submodule.Quotient.induction_on with
        | _ h =>
          change GradedMonoid.mk ((n + p) + q)
            (S.formalGradedMul k (n + p) q (S.formalGradedMul k n p
              (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)) (Submodule.Quotient.mk h)) =
            GradedMonoid.mk (n + (p + q))
            (S.formalGradedMul k n (p + q) (Submodule.Quotient.mk f) (S.formalGradedMul k p q
              (Submodule.Quotient.mk g) (Submodule.Quotient.mk h)))
          simp only [S.formalGradedMul_mk]
          exact S.formal_homogeneous_mk_eq k (Nat.add_assoc n p q) _ _ (mul_assoc _ _ _)
  mul_comm := by
    rintro ⟨n, a⟩ ⟨p, b⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      induction b using Submodule.Quotient.induction_on with
      | _ g =>
        change GradedMonoid.mk (n + p) (S.formalGradedMul k n p
          (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)) =
          GradedMonoid.mk (p + n) (S.formalGradedMul k p n
          (Submodule.Quotient.mk g) (Submodule.Quotient.mk f))
        simp only [S.formalGradedMul_mk]
        exact S.formal_homogeneous_mk_eq k (Nat.add_comm n p) _ _ (mul_comm _ _)
  natCast := fun n => Submodule.Quotient.mk (S.formalZeroRepresentative k n)
  natCast_zero := by
    simp only [Nat.cast_zero]
    rfl
  natCast_succ := by
    intro n
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact Nat.cast_add_one _
  intCast := fun n => Submodule.Quotient.mk (S.formalZeroRepresentative k n)
  intCast_ofNat := by intro n; simp only [Int.cast_natCast]
  intCast_negSucc_ofNat := by
    intro n
    rw [← Submodule.Quotient.mk_neg]
    congr 1

/-- The associated graded ring of actual maximal-ideal powers in k[[S]]. -/
abbrev FormalTangentAlgebra := ⨁ n : ℕ, S.FormalGradedPiece k n

noncomputable instance formalTangentCommRing : CommRing (S.FormalTangentAlgebra k) :=
  DirectSum.commRing (S.FormalGradedPiece k)

theorem formal_tangent_of_mul (n p : ℕ) (a : S.FormalGradedPiece k n) (b : S.FormalGradedPiece k p) :
    DirectSum.of (S.FormalGradedPiece k) n a * DirectSum.of (S.FormalGradedPiece k) p b =
      DirectSum.of (S.FormalGradedPiece k) (n + p) (S.formalGradedMul k n p a b) :=
  DirectSum.of_mul_of a b


end NSP14.NumericalSemigroup
