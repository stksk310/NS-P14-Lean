module

import NSP14
import Mathlib.Data.ZMod.Basic

open NSP14
open scoped BigOperators DirectSum
noncomputable section
namespace NSP14.Block10Audit

private def exampleS : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b c : ℕ, n = 4 * a + 5 * b + 11 * c}
      zero_mem' := ⟨0, 0, 0, by omega⟩
      add_mem' := by
        rintro x y ⟨a, b, c, hx⟩ ⟨d, e, f, hy⟩
        exact ⟨a + d, b + e, c + f, by omega⟩ }
  conductor := 12
  cofinite n hn := by
    have hm := Nat.mod_lt n (by decide : 0 < 4)
    have he := Nat.mod_add_div n 4
    exact ⟨n / 4 - n % 4, n % 4, 0, by omega⟩

private theorem m_four : exampleS.multiplicity = 4 := by
  apply exampleS.multiplicity_eq (by decide) (show 4 ∈ exampleS from ⟨1, 0, 0, by omega⟩)
  rintro x ⟨a, b, c, hx⟩ hpos
  have hsum : 1 ≤ a + b + c := by omega
  omega

private theorem atom_eleven : exampleS.IsAtom 11 := by
  refine ⟨⟨0, 0, 1, by omega⟩, by decide, ?_⟩
  rintro u ⟨a, b, c, hu⟩ v ⟨d, e, f, hv⟩ heq
  have htotal : 4 * (a + d) + 5 * (b + e) + 11 * (c + f) = 11 := by omega
  by_cases hc : c + f = 0
  · have hB : b + e = 0 ∨ b + e = 1 ∨ b + e = 2 := by omega
    rcases hB with h0 | h1 | h2 <;> omega
  · have hcf : c + f = 1 := by omega
    have hzero : a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 := by omega
    have hsplit : c = 0 ∨ f = 0 := by omega
    rcases hsplit with h0 | h0
    · left; omega
    · right; omega

private theorem order_eleven : exampleS.order 11 = 1 := exampleS.atom_order atom_eleven
private theorem order_four : exampleS.order 4 = 1 := by
  simpa [m_four] using exampleS.order_multiplicity

private theorem length_fifteen : exampleS.HasLength 15 3 := by
  have h5 : 5 ∈ exampleS := ⟨0, 1, 0, by omega⟩
  exact ⟨fun _ => 5, fun _ => ⟨h5, by norm_num⟩, by norm_num⟩

private theorem order_fifteen : exampleS.order 15 = 3 := by
  have hlo := exampleS.length_le_order length_fifteen
  have hhi := exampleS.order_bound (show 15 ∈ exampleS from ⟨0, 3, 0, by omega⟩)
  rw [m_four] at hhi
  omega

private theorem order_nineteen : exampleS.order 19 = 4 := by
  have hl4 := exampleS.length_one (show 4 ∈ exampleS from ⟨1, 0, 0, by omega⟩) (by decide)
  have hlen : exampleS.HasLength 19 4 := by simpa using exampleS.length_add hl4 length_fifteen
  have hlo := exampleS.length_le_order hlen
  have hhi := exampleS.order_bound (show 19 ∈ exampleS from ⟨1, 3, 0, by omega⟩)
  rw [m_four] at hhi
  omega

private theorem terminal_eleven : exampleS.Terminal 11 := by
  refine ⟨atom_eleven.1, ?_⟩
  norm_num [m_four, order_eleven, order_fifteen]



private def eleven : exampleS.carrier := ⟨11, atom_eleven.1⟩
private def four : exampleS.carrier := ⟨4, by exact ⟨1, 0, 0, by omega⟩⟩
private def fifteen : exampleS.carrier := ⟨15, by exact ⟨0, 3, 0, by omega⟩⟩
private def eight : exampleS.carrier := four + four
private theorem live_four : exampleS.LiveExponent four := by
  change exampleS.order (4 + exampleS.multiplicity) = exampleS.order 4 + 1
  rw [m_four, order_four]
  change exampleS.order 8 = 2
  have hl := exampleS.order_add four.property four.property
  have hh := exampleS.order_bound eight.property
  change exampleS.order 4 + exampleS.order 4 ≤ exampleS.order 8 at hl
  change exampleS.order 8 * exampleS.multiplicity ≤ 8 at hh
  rw [order_four] at hl
  rw [m_four] at hh
  omega
private theorem head_fifteen : exampleS.XHead 15 := by
  have h := (exampleS.terminal_iff_head 11).1 terminal_eleven
  simpa only [m_four] using h.1
private def head15 : exampleS.HeadExponent := ⟨fifteen, head_fifteen⟩

section General
variable (k : Type*) [CommRing k] [Nontrivial k]

-- Arbitrary coefficients, including zero divisors: no two live arrows collide.
theorem mixed_coordinates (c d : k) :
    exampleS.tangentCoordinates k
      (exampleS.xMultiply k (c • exampleS.initialMonomial k eleven +
        d • exampleS.initialMonomial k four)) =
      Finsupp.single (exampleS.shiftExponent four) d := by
  rw [exampleS.xMultiply_coordinates, map_add, map_smul, map_smul,
    exampleS.tangentCoordinates_initial, exampleS.tangentCoordinates_initial,
    map_add, map_smul, map_smul,
    exampleS.coordinateShift_single_dead k eleven 1
      ((exampleS.not_live_iff_terminal eleven).2 terminal_eleven),
    exampleS.coordinateShift_single_live k four 1 live_four]
  simp

example (c d : k) :
    c • exampleS.initialMonomial k eleven + d • exampleS.initialMonomial k four ∈
      (exampleS.xMultiply k).ker ↔ d = 0 := by
  change exampleS.xMultiply k _ = 0 ↔ _
  rw [← (exampleS.tangentCoordinates k).map_eq_zero_iff, mixed_coordinates]
  exact Finsupp.single_eq_zero

-- A genuine non-Apery head survives; a live incoming coordinate is killed.
omit [Nontrivial k] in
private theorem eight_in_xIdeal : exampleS.initialMonomial k eight ∈ exampleS.xIdeal k := by
  change exampleS.initialMonomial k eight ∈ (exampleS.xIdeal k).restrictScalars k
  rw [exampleS.xIdeal_eq_range]
  refine ⟨exampleS.initialMonomial k four, ?_⟩
  rw [exampleS.xMultiply_initial_live k four live_four]
  congr 1
  apply Subtype.ext
  change 4 + exampleS.multiplicity = 4 + 4
  rw [m_four]

example : Ideal.Quotient.mk (exampleS.xIdeal k) (exampleS.initialMonomial k eight) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (eight_in_xIdeal k)
example : Ideal.Quotient.mk (exampleS.xIdeal k) (exampleS.initialMonomial k fifteen) ≠ 0 :=
  exampleS.head_initial_ne_zero k head15

example (c d : k) :
    exampleS.headQuotientEquiv k (Ideal.Quotient.mk (exampleS.xIdeal k)
      (c • exampleS.initialMonomial k fifteen + d • exampleS.initialMonomial k eight)) =
      Finsupp.single head15 c := by
  have hz : Ideal.Quotient.mk (exampleS.xIdeal k) (exampleS.initialMonomial k eight) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (eight_in_xIdeal k)
  change exampleS.headQuotientEquiv k
    ((Ideal.Quotient.mkₐ k (exampleS.xIdeal k)).toLinearMap
      (c • exampleS.initialMonomial k fifteen + d • exampleS.initialMonomial k eight)) = _
  simp only [map_add, map_smul]
  change c • exampleS.headQuotientEquiv k (Ideal.Quotient.mk (exampleS.xIdeal k)
    (exampleS.initialMonomial k fifteen)) +
    d • exampleS.headQuotientEquiv k (Ideal.Quotient.mk (exampleS.xIdeal k)
    (exampleS.initialMonomial k eight)) = _
  rw [hz, map_zero, smul_zero, add_zero]
  have hh : exampleS.headQuotientEquiv k (Ideal.Quotient.mk (exampleS.xIdeal k)
      (exampleS.initialMonomial k fifteen)) = Finsupp.single head15 1 :=
    exampleS.headQuotientEquiv_initial k head15
  rw [hh]
  simp

-- The actual quotient, with its inherited k-algebra, has a nonzero identity.
example : (1 : exampleS.HeadAlgebra k) ≠ 0 := by
  have h0 : exampleS.XHead 0 := by
    refine ⟨exampleS.zero_mem, ?_⟩
    rintro ⟨x, hx, heq, _⟩
    have hp := exampleS.multiplicity_pos
    omega
  have hi : exampleS.initialMonomial k (0 : exampleS.carrier) = 1 := by
    unfold NumericalSemigroup.initialMonomial
    rw [DirectSum.one_def]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply exampleS.homogeneous_mk_eq k exampleS.order_zero
    rfl
  have hh := exampleS.head_initial_ne_zero k (⟨0, h0⟩ : exampleS.HeadExponent)
  simpa only [hi, map_one] using hh
end General

-- Scalar and integer embeddings agree with the original quotient module action.
example (S : NumericalSemigroup) (k : Type*) [CommRing k] (r : k) :
    algebraMap k (S.TangentAlgebra k) r = r • (1 : S.TangentAlgebra k) :=
  Algebra.algebraMap_eq_smul_one r
example (S : NumericalSemigroup) (k : Type*) [CommRing k] (a : S.TangentAlgebra k) :
    (-1 : S.TangentAlgebra k) * a = -a := neg_one_mul a
example (S : NumericalSemigroup) (k : Type*) [CommRing k] (a : S.TangentAlgebra k) :
    (-1 : k) • a = -a := neg_one_smul k a

-- The algebraic constructions are still defined over a trivial coefficient ring.
example (S : NumericalSemigroup) (a : S.TangentAlgebra (ZMod 1)) : a = 0 :=
  (S.tangentCoordinates (ZMod 1)).injective (Subsingleton.elim _ _)

-- Composite characteristic is included in the full-kernel/head interfaces.
local instance : Fact (1 < 4) := ⟨by decide⟩
example : (exampleS.xMultiply (ZMod 4)).ker ≃ₗ[ZMod 4]
    (exampleS.TerminalExponent →₀ ZMod 4) := exampleS.xKernelEquiv (ZMod 4)
example : exampleS.HeadAlgebra (ZMod 4) ≃ₗ[ZMod 4]
    (exampleS.HeadExponent →₀ ZMod 4) := exampleS.headQuotientEquiv (ZMod 4)

#print axioms mixed_coordinates
#print axioms eight_in_xIdeal
end NSP14.Block10Audit
