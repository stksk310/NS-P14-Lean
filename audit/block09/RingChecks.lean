module

import NSP14
import Mathlib.Data.ZMod.Basic

open NSP14
open scoped BigOperators

noncomputable section
namespace NSP14.Block09Audit

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


-- All actual constructions remain available over an arbitrary commutative ring.
section GeneralRing
variable (S : NumericalSemigroup) (k : Type*) [CommRing k]
example (n : ℕ) : S.orderIdeal k n = S.positiveIdeal k ^ n := S.orderIdeal_eq_pow k n
example (n : ℕ) : S.GradedPiece k n ≃ₗ[k] (S.DegreeExponent n →₀ k) :=
  S.gradedPieceEquiv k n
example (n : ℕ) (x : S.carrier) :
    AddMonoidAlgebra.single x (0 : k) ∈ S.positiveIdeal k ^ n := by simp
example (x : S.carrier) (h : S.order x.val = 0) : x = 0 :=
  Subtype.ext ((S.order_eq_zero_iff x.property).1 h)
end GeneralRing

private def eleven : exampleS.carrier := ⟨11, atom_eleven.1⟩
private def fifteen : exampleS.carrier := ⟨15, by exact ⟨0, 3, 0, by omega⟩⟩
private def four : exampleS.carrier := ⟨4, by exact ⟨1, 0, 0, by omega⟩⟩

-- A genuinely terminal generator is nonzero in its own layer, but killed by x.
example (k : Type*) [CommRing k] [Nontrivial k] :
    exampleS.monomialClass k (exampleS.order eleven.val) eleven le_rfl ≠ 0 :=
  exampleS.monomialClass_ne_zero k eleven
example (k : Type*) [CommRing k] [Nontrivial k] :
    exampleS.xAction k (exampleS.order eleven.val)
      (exampleS.monomialClass k _ eleven le_rfl) = 0 :=
  (exampleS.xAction_monomial_eq_zero_iff k eleven).2 terminal_eleven
example (k : Type*) [CommRing k] [Nontrivial k] :
    exampleS.xAction k (exampleS.order four.val)
      (exampleS.monomialClass k _ four le_rfl) ≠ 0 := by
  apply (exampleS.xAction_monomial_ne_zero_iff k four).2
  change exampleS.order (4 + exampleS.multiplicity) = exampleS.order 4 + 1
  rw [m_four, order_four]
  have hl := exampleS.order_add four.property four.property
  have hh := exampleS.order_bound (exampleS.carrier.add_mem four.property four.property)
  change exampleS.order 4 + exampleS.order 4 ≤ exampleS.order 8 at hl
  change exampleS.order 8 * exampleS.multiplicity ≤ 8 at hh
  rw [order_four] at hl
  rw [m_four] at hh
  change exampleS.order 8 = 2
  omega

-- Coefficient cancellation must remove the low-order term from the support.
example : AddMonoidAlgebra.single eleven (1 : ℚ) ∉ exampleS.positiveIdeal ℚ ^ 2 := by
  rw [exampleS.monomial_mem_pow_iff]
  change ¬ 2 ≤ exampleS.order 11
  rw [order_eleven]
  decide
example : ((AddMonoidAlgebra.single eleven (1 : ℚ) + AddMonoidAlgebra.single fifteen 1)
    - AddMonoidAlgebra.single eleven 1) ∈ exampleS.positiveIdeal ℚ ^ 3 := by
  have heq : ((AddMonoidAlgebra.single eleven (1 : ℚ) + AddMonoidAlgebra.single fifteen 1)
      - AddMonoidAlgebra.single eleven 1) = AddMonoidAlgebra.single fifteen 1 := by abel
  rw [heq, exampleS.monomial_mem_pow_iff]
  change 3 ≤ exampleS.order 15
  rw [order_fifteen]

-- Nontriviality is substantive: over the zero ring every monomial class vanishes.
example (S : NumericalSemigroup) (x : S.carrier) :
    S.monomialClass (ZMod 1) (S.order x.val) x le_rfl = 0 := Subsingleton.elim _ _

-- A composite-characteristic coefficient ring is allowed. A live monomial with
-- a nonunit coefficient may have square zero; the source's survival theorem
-- correctly concerns coefficient 1, rather than arbitrary nonzero coefficients.
private def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite _ _ := by trivial
private def oneExponent : naturals.carrier := ⟨1, by trivial⟩
local instance : Fact (1 < 4) := ⟨by decide⟩
private theorem nat_order (x : ℕ) : naturals.order x = x := by
  have hl : naturals.HasLength x x :=
    ⟨fun _ => 1, fun _ => ⟨by trivial, by norm_num⟩, by simp⟩
  have h := naturals.length_le_order hl
  have hh := naturals.length_le (naturals.order_length (show x ∈ naturals from by trivial))
  omega
example : naturals.gradedMul (ZMod 4) (naturals.order oneExponent.val)
    (naturals.order oneExponent.val) (naturals.monomialClass (ZMod 4) _ oneExponent le_rfl)
      (naturals.monomialClass (ZMod 4) _ oneExponent le_rfl) ≠ 0 := by
  apply (naturals.gradedMul_monomial_ne_zero_iff (ZMod 4) oneExponent oneExponent).2
  simp only [nat_order]
example : naturals.gradedMul (ZMod 4) (naturals.order oneExponent.val)
    (naturals.order oneExponent.val)
      ((2 : ZMod 4) • naturals.monomialClass (ZMod 4) _ oneExponent le_rfl)
      ((2 : ZMod 4) • naturals.monomialClass (ZMod 4) _ oneExponent le_rfl) = 0 := by
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [show (2 : ZMod 4) * 2 = 0 by decide]
  exact zero_smul _ _

-- C=0 is the sharp natural-semigroup boundary of the coarse finiteness estimate.
example (n : ℕ) : naturals.order n < n + 1 := by rw [nat_order]; omega
example (n : ℕ) : n < (n + 1) * (naturals.conductor + 1) := by
  exact naturals.order_level_bound n n (by rw [nat_order])

#print axioms exampleS
#print axioms terminal_eleven
end NSP14.Block09Audit
