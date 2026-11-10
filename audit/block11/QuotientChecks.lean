module

import NSP14
import Mathlib.Data.ZMod.Basic

open NSP14
open scoped BigOperators Classical
noncomputable section
namespace NSP14.Block11Audit

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


private theorem fifteen_nonapery : fifteen.val ∉ exampleS.aperySet := by
  intro h
  exact exampleS.apery_no_predecessor h ⟨11, eleven.property, by rw [m_four]; rfl⟩

section General
variable (k : Type*) [CommRing k] [Nontrivial k]

-- Degree three is a sharp failure of the low-degree injectivity claim.
example : ¬ Function.Injective (exampleS.headToQDegree k 3) := by
  intro hi
  let a : exampleS.headDegree k 3 :=
    ⟨exampleS.headMonomial k fifteen,
      exampleS.headMonomial_mem_degree k fifteen 3 order_fifteen⟩
  have hmap : exampleS.headToQDegree k 3 a = exampleS.headToQDegree k 3 0 := by
    apply Subtype.ext
    change exampleS.qMonomial k fifteen = 0
    exact exampleS.qMonomial_zero_of_nonapery k fifteen fifteen_nonapery
  have hzero := congrArg Subtype.val (hi hmap)
  exact exampleS.head_initial_ne_zero k head15 hzero

example (a : exampleS.HeadAlgebra k) :
    (exampleS.aperyProjection k a = 0) ↔ a ∈ exampleS.nonAperyIdeal k := by
  change a ∈ (exampleS.aperyProjection k).ker ↔ _
  rw [exampleS.aperyProjection_ker]
  rfl

-- The grading is inherited: its registered projection preserves N on all inputs.
example (n : ℕ) (a : exampleS.HeadAlgebra k) (ha : a ∈ exampleS.nonAperyIdeal k) :
    GradedAlgebra.proj (R := k) (A := exampleS.HeadAlgebra k) (exampleS.headDegree k) n a ∈
      exampleS.nonAperyIdeal k := by
  rw [← exampleS.headGradeProject_eq_proj]
  exact exampleS.headGradeProject_mem_nonAperyIdeal k n a ha

-- The low-degree equivalence is the natural quotient map, including n=0.
example (n : ℕ) (hn : n ≤ 2) (a : exampleS.headDegree k n) :
    (exampleS.lowDegreeQuotientEquiv k n hn a).val =
      Ideal.Quotient.mk (exampleS.nonAperyIdeal k) a.val := rfl

-- Mixed degrees cannot cancel; the registered grading retains degree uniqueness.
example (a : exampleS.AperyAlgebra k) (h1 : a ∈ exampleS.qDegree k 1)
    (h2 : a ∈ exampleS.qDegree k 2) : a = 0 := by
  apply (exampleS.aperyQuotientEquiv k).injective
  ext x
  have ha := (exampleS.mem_qDegree_coordinates k 1 a).1 h1
  have hb := (exampleS.mem_qDegree_coordinates k 2 a).1 h2
  by_cases h : exampleS.order x.val.val = 1
  · exact (Finsupp.mem_supported' k _).1 hb x (by change exampleS.order x.val.val ≠ 2; omega)
  · exact (Finsupp.mem_supported' k _).1 ha x h
end General

-- Independent <5,6,9>, with a deliberately nonminimal conductor witness 25.
-- Here 18 is Apery but [9]^2=0: membership of the sum alone is insufficient.
private def delayed : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b c : ℕ, n = 5*a + 6*b + 9*c}
      zero_mem' := ⟨0,0,0,by omega⟩
      add_mem' := by
        rintro x y ⟨a,b,c,hx⟩ ⟨d,e,f,hy⟩
        exact ⟨a+d,b+e,c+f,by omega⟩ }
  conductor := 25
  cofinite n hn := by
    have hr := Nat.mod_lt n (by decide : 0 < 5)
    have he := Nat.mod_add_div n 5
    exact ⟨n/5-n%5,n%5,0,by omega⟩
private theorem delayed_m : delayed.multiplicity = 5 := by
  apply delayed.multiplicity_eq (by decide) (show 5 ∈ delayed from ⟨1,0,0,by omega⟩)
  rintro x ⟨a,b,c,hx⟩ hp
  have hsum : 1 ≤ a+b+c := by omega
  omega
private def nine : delayed.carrier := ⟨9,0,0,1,by omega⟩
private def eighteen : delayed.carrier := ⟨18,0,3,0,by omega⟩
private theorem delayed_order_nine : delayed.order 9 = 1 := by
  have hlo := delayed.order_pos nine.property (by decide : 0<9)
  have hhi := delayed.order_bound nine.property
  change delayed.order 9 * delayed.multiplicity ≤ 9 at hhi
  change 0 < delayed.order 9 at hlo
  rw [delayed_m] at hhi
  omega
private theorem delayed_order_eighteen : delayed.order 18 = 3 := by
  have h6 : 6 ∈ delayed := ⟨0,1,0,by omega⟩
  have hlo := delayed.length_le_order
    (show delayed.HasLength 18 3 from ⟨fun _ => 6,fun _ => ⟨h6,by norm_num⟩,by norm_num⟩)
  have hhi := delayed.order_bound eighteen.property
  change delayed.order 18 * delayed.multiplicity ≤ 18 at hhi
  rw [delayed_m] at hhi
  omega
private theorem eighteen_apery : eighteen.val ∈ delayed.aperySet := by
  apply (delayed.mem_apery_iff_no_predecessor eighteen.property).2
  rintro ⟨y,⟨a,b,c,hy⟩,heq⟩
  change 18 = y + delayed.multiplicity at heq
  rw [delayed_m] at heq
  omega

example : (nine+nine).val ∈ delayed.aperySet := eighteen_apery
example (k : Type*) [CommRing k] [Nontrivial k] :
    delayed.qMonomial k nine * delayed.qMonomial k nine = 0 := by
  apply delayed.qMonomial_mul_dead
  change delayed.order 9 + delayed.order 9 < delayed.order 18
  rw [delayed_order_nine, delayed_order_eighteen]
  decide
example (k : Type*) [CommRing k] [Nontrivial k] : delayed.qMonomial k eighteen ≠ 0 :=
  delayed.qMonomial_ne_zero k ⟨eighteen,eighteen_apery⟩
example (k : Type*) [CommRing k] [Nontrivial k] : delayed.qDegree k 3 ≠ ⊥ := by
  intro h
  have hm := delayed.qMonomial_mem_degree k eighteen 3 delayed_order_eighteen
  rw [h] at hm
  exact delayed.qMonomial_ne_zero k ⟨eighteen,eighteen_apery⟩ hm

-- Composite characteristic retains the registered grading and standard generation.
local instance : Fact (1 < 4) := ⟨by decide⟩
example : GradedAlgebra (R := ZMod 4) (A := delayed.AperyAlgebra (ZMod 4))
    (delayed.qDegree (ZMod 4)) := inferInstance
example : delayed.aperyAtomSubalgebra (ZMod 4) = ⊤ := delayed.apery_atom_adjoin_top (ZMod 4)

#print axioms eighteen_apery
#print axioms delayed_order_eighteen
end NSP14.Block11Audit
