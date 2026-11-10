module

public import NSP14.Semigroup.GradedPieces
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- Multiplication of representatives, followed by the homogeneous quotient map. -/
noncomputable def representativeProduct (n p : ℕ) :
    S.powerModule k n →ₗ[k] S.powerModule k p →ₗ[k] S.GradedPiece k (n + p) where
  toFun f :=
    { toFun := fun g => Submodule.Quotient.mk ⟨f.val * g.val,
        by
          change f.val * g.val ∈ S.positiveIdeal k ^ (n + p)
          rw [pow_add]
          exact Ideal.mul_mem_mul f.property g.property⟩
      map_add' := by intros; simp [mul_add]; rfl
      map_smul' := by intros; simp; rfl }
  map_add' := by intros; ext; simp [add_mul]; rfl
  map_smul' := by intros; ext; simp; rfl

theorem representativeProduct_left_zero (n p : ℕ) :
    S.nextPower k n ≤ (S.representativeProduct k n p).ker := by
  intro f hf
  ext g
  rw [LinearMap.zero_apply]
  change (Submodule.Quotient.mk _ : S.GradedPiece k (n + p)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change f.val * g.val ∈ S.positiveIdeal k ^ (n + p + 1)
  have hf' : f.val ∈ S.positiveIdeal k ^ (n + 1) := hf
  have hm := Ideal.mul_mem_mul hf' g.property
  simpa [← pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem representativeProduct_right_zero (n p : ℕ) :
    S.nextPower k p ≤ (S.representativeProduct k n p).flip.ker := by
  intro g hg
  ext f
  rw [LinearMap.zero_apply]
  change (Submodule.Quotient.mk _ : S.GradedPiece k (n + p)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change f.val * g.val ∈ S.positiveIdeal k ^ (n + p + 1)
  have hg' : g.val ∈ S.positiveIdeal k ^ (p + 1) := hg
  have hm := Ideal.mul_mem_mul f.property hg'
  simpa [← pow_add, Nat.add_assoc] using hm

/-- Well-defined multiplication of homogeneous pieces of the actual associated graded. -/
noncomputable def gradedMul (n p : ℕ) :
    S.GradedPiece k n →ₗ[k] S.GradedPiece k p →ₗ[k] S.GradedPiece k (n + p) :=
  (S.representativeProduct k n p).liftQ₂ (S.nextPower k n) (S.nextPower k p)
    (S.representativeProduct_left_zero k n p) (S.representativeProduct_right_zero k n p)

theorem gradedMul_mk (n p : ℕ) (f : S.powerModule k n) (g : S.powerModule k p) :
    S.gradedMul k n p (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk ⟨f.val * g.val,
        by
          change f.val * g.val ∈ S.positiveIdeal k ^ (n + p)
          rw [pow_add]
          exact Ideal.mul_mem_mul f.property g.property⟩ := rfl

theorem gradedMul_monomial_layers (n p : ℕ) (x y : S.carrier)
    (hx : n ≤ S.order x.val) (hy : p ≤ S.order y.val) :
    S.gradedMul k n p (S.monomialClass k n x hx) (S.monomialClass k p y hy) =
      S.monomialClass k (n + p) (x + y)
        ((Nat.add_le_add hx hy).trans (S.order_add x.property y.property)) := by
  simp only [monomialClass, gradedMul_mk, AddMonoidAlgebra.single_mul_single, one_mul]

theorem gradedMul_monomial (x y : S.carrier) :
    S.gradedMul k (S.order x.val) (S.order y.val)
      (S.monomialClass k _ x le_rfl) (S.monomialClass k _ y le_rfl) =
    S.monomialClass k (S.order x.val + S.order y.val) (x + y)
      (S.order_add x.property y.property) := by
  simp only [monomialClass, gradedMul_mk, AddMonoidAlgebra.single_mul_single, one_mul]

theorem gradedMul_monomial_eq_zero_iff [Nontrivial k] (x y : S.carrier) :
    S.gradedMul k (S.order x.val) (S.order y.val)
      (S.monomialClass k _ x le_rfl) (S.monomialClass k _ y le_rfl) = 0 ↔
      S.order x.val + S.order y.val < S.order (x.val + y.val) := by
  rw [S.gradedMul_monomial, S.product_class_eq_zero_iff]

theorem gradedMul_monomial_ne_zero_iff [Nontrivial k] (x y : S.carrier) :
    S.gradedMul k (S.order x.val) (S.order y.val)
      (S.monomialClass k _ x le_rfl) (S.monomialClass k _ y le_rfl) ≠ 0 ↔
      S.order (x.val + y.val) = S.order x.val + S.order y.val := by
  simp only [ne_eq, S.gradedMul_monomial_eq_zero_iff]
  have := S.order_add x.property y.property
  omega

end NSP14.NumericalSemigroup
