module

import NSP14

noncomputable section

open NSP14 NSP14.NumericalSemigroup
open scoped BigOperators

section Interfaces
variable (S : NumericalSemigroup) (k : Type*) [Field k]

example (n : ℕ) : S.orderIdeal k n = S.positiveIdeal k ^ n := S.orderIdeal_eq_pow k n
example (n : ℕ) (f : S.SemigroupRing k) :
    f ∈ S.positiveIdeal k ^ n ↔ ∀ x, S.order x.val < n → f.coeff x = 0 :=
  S.mem_positiveIdeal_pow k n f
example : (S.positiveIdeal k).IsMaximal := S.positiveIdeal_isMaximal k
example (n : ℕ) : S.GradedPiece k n ≃ₗ[k] (S.DegreeExponent n →₀ k) := S.gradedPieceEquiv k n
example (n : ℕ) : Finite (S.DegreeExponent n) := inferInstance
example (n : ℕ) : Module.Basis (S.DegreeExponent n) k (S.GradedPiece k n) := S.gradedPieceBasis k n
example (x : S.carrier) :
    S.monomialClass k (S.order x.val) x le_rfl ∈ (S.xAction k (S.order x.val)).ker ↔
    S.Terminal x.val := S.monomial_mem_xKernel_iff k x
example (x y : S.carrier) :
    S.gradedMul k _ _ (S.monomialClass k _ x le_rfl) (S.monomialClass k _ y le_rfl) ≠ 0 ↔
    S.order (x.val + y.val) = S.order x.val + S.order y.val :=
  S.gradedMul_monomial_ne_zero_iff k x y
end Interfaces

namespace RingExamples

def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite _ _ := by trivial

theorem naturals_m : naturals.multiplicity = 1 :=
  naturals.multiplicity_eq (by decide) (by trivial) (by intro x _ hx; omega)

theorem naturals_order (x : ℕ) : naturals.order x = x := by
  have hlen : naturals.HasLength x x :=
    ⟨fun _ => 1, fun _ => ⟨by trivial, by norm_num⟩, by simp⟩
  have hlo := naturals.length_le_order hlen
  have hhi := naturals.order_bound (show x ∈ naturals from by trivial)
  rw [naturals_m, mul_one] at hhi
  omega

example (n : ℕ) (f : naturals.SemigroupRing ℚ) :
    f ∈ naturals.positiveIdeal ℚ ^ n ↔ ∀ x, x.val < n → f.coeff x = 0 := by
  simpa only [naturals_order] using naturals.mem_positiveIdeal_pow ℚ n f

example (x : naturals.carrier) :
    naturals.xAction ℚ (naturals.order x.val) (naturals.monomialClass ℚ _ x le_rfl) ≠ 0 := by
  rw [naturals.xAction_monomial_ne_zero_iff]
  simp only [naturals_order, naturals_m]

/-- The actual semigroup <2,3>, with a valid conductor witness 2. -/
def cusp : NumericalSemigroup where
  carrier :=
    { carrier := {n | n = 0 ∨ 2 ≤ n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro x y (hx | hx) (hy | hy) <;>
          change x + y = 0 ∨ 2 ≤ x + y <;> omega }
  conductor := 2
  cofinite _ hn := Or.inr hn

theorem cusp_m : cusp.multiplicity = 2 := by
  apply cusp.multiplicity_eq (by decide) (show 2 ∈ cusp from Or.inr (by decide))
  rintro x (hx | hx) hp <;> omega

def a : cusp.carrier := ⟨2, Or.inr (by decide)⟩
def b : cusp.carrier := ⟨3, Or.inr (by decide)⟩

theorem cusp_order_two : cusp.order 2 = 1 := by
  simpa only [cusp_m] using cusp.order_multiplicity

theorem cusp_order_three : cusp.order 3 = 1 := by
  have hl := cusp.order_pos b.property (by decide : 0 < 3)
  have hu := cusp.order_bound b.property
  change cusp.order 3 * cusp.multiplicity ≤ 3 at hu
  change 1 ≤ cusp.order 3 at hl
  rw [cusp_m] at hu
  omega

theorem cusp_order_four : cusp.order 4 = 2 := by
  have hl := cusp.order_add a.property a.property
  change cusp.order 2 + cusp.order 2 ≤ cusp.order 4 at hl
  have hu := cusp.order_bound (show 4 ∈ cusp from Or.inr (by decide))
  rw [cusp_m] at hu
  rw [cusp_order_two] at hl
  omega

theorem cusp_order_six : cusp.order 6 = 3 := by
  have hlen : cusp.HasLength 6 3 :=
    ⟨fun _ => 2, fun _ => ⟨Or.inr (by norm_num), by norm_num⟩, by norm_num⟩
  have hl := cusp.length_le_order hlen
  have hu := cusp.order_bound (show 6 ∈ cusp from Or.inr (by decide))
  rw [cusp_m] at hu
  omega

-- Nonadditive order causes a genuine zero product in the homogeneous quotient.
example : cusp.gradedMul ℚ (cusp.order b.val) (cusp.order b.val)
    (cusp.monomialClass ℚ _ b le_rfl) (cusp.monomialClass ℚ _ b le_rfl) = 0 := by
  rw [cusp.gradedMul_monomial_eq_zero_iff]
  change cusp.order 3 + cusp.order 3 < cusp.order 6
  rw [cusp_order_three, cusp_order_six]
  decide

-- Additive order gives a nonzero product in the same actual quotient construction.
example : cusp.gradedMul ℚ (cusp.order a.val) (cusp.order a.val)
    (cusp.monomialClass ℚ _ a le_rfl) (cusp.monomialClass ℚ _ a le_rfl) ≠ 0 := by
  apply (cusp.gradedMul_monomial_ne_zero_iff ℚ a a).2
  change cusp.order 4 = cusp.order 2 + cusp.order 2
  rw [cusp_order_four, cusp_order_two]

example : AddMonoidAlgebra.single b (1 : ℚ) ∉ cusp.positiveIdeal ℚ ^ 2 := by
  intro h
  have := (cusp.monomial_mem_pow_iff ℚ 2 b).1 h
  change 2 ≤ cusp.order 3 at this
  rw [cusp_order_three] at this
  omega

example : AddMonoidAlgebra.single (b + b) (1 : ℚ) ∈ cusp.positiveIdeal ℚ ^ 3 := by
  apply (cusp.monomial_mem_pow_iff ℚ 3 (b + b)).2
  change 3 ≤ cusp.order 6
  rw [cusp_order_six]

example (f : cusp.SemigroupRing ℚ) (n : ℕ) : f - f ∈ cusp.positiveIdeal ℚ ^ n := by simp
example : (cusp.positiveIdeal ℚ).IsMaximal := cusp.positiveIdeal_isMaximal ℚ
example : cusp.orderIdeal ℚ 0 = ⊤ := cusp.orderIdeal_zero ℚ
example : (cusp.constantCoeff ℚ) (AddMonoidAlgebra.single (0 : cusp.carrier) (7 : ℚ)) = 7 := by
  change (AddMonoidAlgebra.single (0 : cusp.carrier) (7 : ℚ)).coeff 0 = 7
  simp

example (n : ℕ) (x : cusp.carrier) :
    AddMonoidAlgebra.single x (0 : ℚ) ∈ cusp.positiveIdeal ℚ ^ n := by simp

example : cusp.monomialClass ℚ 0 (0 : cusp.carrier) (Nat.zero_le _) ≠ 0 := by
  intro h
  have hx := (cusp.monomialClass_eq_zero_iff ℚ 0 0 (Nat.zero_le _)).1 h
  change 0 < cusp.order 0 at hx
  simp only [cusp.order_zero, Nat.lt_irrefl] at hx

end RingExamples

-- Audit every new named definition, theorem and finite-instance proof.
#print axioms NSP14.NumericalSemigroup.SemigroupRing
#print axioms NSP14.NumericalSemigroup.orderIdeal
#print axioms NSP14.NumericalSemigroup.positiveIdeal
#print axioms NSP14.NumericalSemigroup.mem_orderIdeal_iff
#print axioms NSP14.NumericalSemigroup.mem_orderIdeal_coeff
#print axioms NSP14.NumericalSemigroup.single_mem_orderIdeal
#print axioms NSP14.NumericalSemigroup.single_mem_orderIdeal_iff
#print axioms NSP14.NumericalSemigroup.orderIdeal_antitone
#print axioms NSP14.NumericalSemigroup.orderIdeal_zero
#print axioms NSP14.NumericalSemigroup.orderIdeal_one
#print axioms NSP14.NumericalSemigroup.mem_of_support_single_mem
#print axioms NSP14.NumericalSemigroup.orderIdeal_mul_le
#print axioms NSP14.NumericalSemigroup.positive_single_mem
#print axioms NSP14.NumericalSemigroup.single_sum_mem_pow
#print axioms NSP14.NumericalSemigroup.single_order_mem_pow
#print axioms NSP14.NumericalSemigroup.positiveIdeal_pow_le
#print axioms NSP14.NumericalSemigroup.orderIdeal_eq_pow
#print axioms NSP14.NumericalSemigroup.mem_positiveIdeal_pow
#print axioms NSP14.NumericalSemigroup.monomial_mem_pow_iff
#print axioms NSP14.NumericalSemigroup.mem_positiveIdeal
#print axioms NSP14.NumericalSemigroup.constantCoeff_mul
#print axioms NSP14.NumericalSemigroup.constantCoeff
#print axioms NSP14.NumericalSemigroup.constantCoeff_surjective
#print axioms NSP14.NumericalSemigroup.constantCoeff_ker
#print axioms NSP14.NumericalSemigroup.positiveIdeal_isMaximal
#print axioms NSP14.NumericalSemigroup.positive_atom_summand
#print axioms NSP14.NumericalSemigroup.positiveIdeal_eq_atom_span
#print axioms NSP14.NumericalSemigroup.powerModule
#print axioms NSP14.NumericalSemigroup.nextPower
#print axioms NSP14.NumericalSemigroup.GradedPiece
#print axioms NSP14.NumericalSemigroup.DegreeExponent
#print axioms NSP14.NumericalSemigroup.leadingMap
#print axioms NSP14.NumericalSemigroup.leadingMap_apply
#print axioms NSP14.NumericalSemigroup.leadingMap_ker
#print axioms NSP14.NumericalSemigroup.leadingMap_surjective
#print axioms NSP14.NumericalSemigroup.gradedPieceEquiv
#print axioms NSP14.NumericalSemigroup.gradedPieceEquiv_mk
#print axioms NSP14.NumericalSemigroup.monomialClass
#print axioms NSP14.NumericalSemigroup.monomialClass_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.monomialClass_ne_zero
#print axioms NSP14.NumericalSemigroup.product_class_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.representativeProduct
#print axioms NSP14.NumericalSemigroup.representativeProduct_left_zero
#print axioms NSP14.NumericalSemigroup.representativeProduct_right_zero
#print axioms NSP14.NumericalSemigroup.gradedMul
#print axioms NSP14.NumericalSemigroup.gradedMul_mk
#print axioms NSP14.NumericalSemigroup.gradedMul_monomial_layers
#print axioms NSP14.NumericalSemigroup.gradedMul_monomial
#print axioms NSP14.NumericalSemigroup.gradedMul_monomial_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.gradedMul_monomial_ne_zero_iff
#print axioms NSP14.NumericalSemigroup.order_level_bound
#print axioms NSP14.NumericalSemigroup.degreeExponentFinite
#print axioms NSP14.NumericalSemigroup.gradedPieceBasis
#print axioms NSP14.NumericalSemigroup.gradedPieceBasis_coordinates
#print axioms NSP14.NumericalSemigroup.gradedPieceBasis_eq_monomial
#print axioms NSP14.NumericalSemigroup.multiplicityExponent
#print axioms NSP14.NumericalSemigroup.xAction
#print axioms NSP14.NumericalSemigroup.xAction_monomial_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.xAction_monomial_ne_zero_iff
#print axioms NSP14.NumericalSemigroup.monomial_mem_xKernel_iff
