module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Abel
public import NSP14.Ordinary.SmallScalar

@[expose] public section

namespace NSP14

/-- Unordered two-term sums are unique, including repeated summands. -/
def IsSidon {G : Type*} [Add G] (B : Finset G) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The difference map is injective on ordered pairs of distinct points. -/
theorem sidon_difference_injective {G : Type*} [AddCommGroup G]
    (B : Finset G) (hB : IsSidon B) :
    Set.InjOn (fun p : G × G => p.1 - p.2) (B.offDiag : Set (G × G)) := by
  intro p hp q hq heq
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hc, hd, _⟩ := Finset.mem_offDiag.mp hq
  have hs : p.1 + q.2 = q.1 + p.2 := by
    have h := sub_eq_sub_iff_add_eq_add.mp heq
    simpa [add_comm] using h
  rcases hB p.1 ha q.2 hd q.1 hc p.2 hb hs with h | h
  · exact Prod.ext h.1 h.2.symm
  · exact (hab h.1).elim

/-- No primality or oddness assumption on m: differences inject into nonzero residues. -/
theorem sidon_card_bound (m : ℕ) [NeZero m] (B : Finset (ZMod m))
    (hB : IsSidon B) : B.card * (B.card - 1) ≤ m - 1 := by
  classical
  have hle : B.offDiag.card ≤ (Finset.univ.erase (0 : ZMod m)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ZMod m × ZMod m => p.1 - p.2)
    · intro p hp
      have hne := (Finset.mem_offDiag.mp hp).2.2
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      exact sub_ne_zero.mpr hne
    · exact sidon_difference_injective B hB
  simpa [Finset.offDiag_card, Nat.mul_sub_left_distrib, ZMod.card] using hle

/-- Actual numerical minimum in a residue class of an additive submonoid of N.
No abstract Hilbert profile or algebraic quotient is used in this definition. -/
def IsAperyMin (S : AddSubmonoid ℕ) (m x : ℕ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, y % m = x % m → x ≤ y

/-- Equal residues of actual Apéry minima have equal numerical values. -/
theorem apery_min_unique {S : AddSubmonoid ℕ} {m x y : ℕ}
    (hx : IsAperyMin S m x) (hy : IsAperyMin S m y)
    (h : x % m = y % m) : x = y := by
  exact Nat.le_antisymm (hx.2 y hy.1 h.symm) (hy.2 x hx.1 h)

/-- Numeric data to be constructed from the future maximal quadratic Apéry quotient.
The minimal representatives and uniqueness are explicit proof fields, not axioms.
This is not yet a construction of a semigroup's tangent cone or its Q2. -/
structure AperyPairData (S : AddSubmonoid ℕ) (m e : ℕ) where
  value : Fin e → ℕ
  injective_value : Function.Injective value
  value_min : ∀ i, IsAperyMin S m (value i)
  pair_min : ∀ i j, IsAperyMin S m (value i + value j)
  pair_unique : ∀ i j k l, value i + value j = value k + value l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)

namespace AperyPairData

variable {S : AddSubmonoid ℕ} {m e : ℕ} (D : AperyPairData S m e)

def residue (i : Fin e) : ZMod m := D.value i

theorem residue_injective : Function.Injective D.residue := by
  intro i j h
  apply D.injective_value
  apply apery_min_unique (D.value_min i) (D.value_min j)
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h

noncomputable def residues : Finset (ZMod m) :=
  (Finset.univ : Finset (Fin e)).image D.residue

theorem residues_card : D.residues.card = e := by
  classical
  simp only [residues, Finset.card_image_of_injective _ D.residue_injective,
    Finset.card_univ, Fintype.card_fin]

theorem residues_sidon : IsSidon D.residues := by
  classical
  intro a ha b hb c hc d hd heq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
  have hcast : ((D.value i + D.value j : ℕ) : ZMod m) =
      ((D.value k + D.value l : ℕ) : ZMod m) := by
    simpa [residue, Nat.cast_add] using heq
  have hnum := apery_min_unique (D.pair_min i j) (D.pair_min k l)
    ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast)
  rcases D.pair_unique i j k l hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst k; subst l; exact Or.inl ⟨rfl, rfl⟩
  · subst l; subst k; exact Or.inr ⟨rfl, rfl⟩

include D in
theorem multiplicity_bound [NeZero m] : e * (e - 1) + 1 ≤ m := by
  have h := sidon_card_bound m D.residues D.residues_sidon
  rw [D.residues_card] at h
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  omega

include D in
/-- The SO1 deficit bound, derived from the proved residue count. -/
theorem deficit_bound [NeZero m] (d : ℕ) (he : 1 ≤ e) (hm : m = e + d) :
    (e - 1) ^ 2 ≤ d := by
  have h := D.multiplicity_bound
  have heq : e - 1 + 1 = e := Nat.sub_add_cancel he
  rw [hm] at h
  nlinarith

end AperyPairData

namespace Ordinary.SmallScalar

/-- Sidon data rule out exactly the corners needed by Block 01. -/
theorem corner_condition_of_sidon (m r s t : ℕ) [NeZero m]
    (B : Finset (ZMod m)) (hB : IsSidon B)
    (hcard : B.card = r + 1 + s)
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8) : r ≤ 5 ∨ s + t ≠ 0 := by
  by_cases hl : r ≤ 5
  · exact Or.inl hl
  right
  intro hzero
  have hs : s = 0 := by omega
  have ht : t = 0 := by omega
  subst s; subst t
  have hc := sidon_card_bound m B hB
  rw [hcard] at hc
  obtain ⟨hlo, hhi⟩ := hr
  have h6 : 6 ≤ r := by omega
  interval_cases r <;> norm_num at hm hc <;> omega

/-- Block 01 connected to a proved Sidon witness, with no separate bad-corner premise. -/
theorem small_gap_pos_of_sidon (m r s t : ℕ) [NeZero m]
    (B : Finset (ZMod m)) (hB : IsSidon B)
    (hcard : B.card = r + 1 + s)
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8) :
    0 < gap r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t) := by
  exact small_gap_pos r s t hr (corner_condition_of_sidon m r s t B hB hcard hm hr)

/-- Only maximal-cut boundary points require a Sidon witness; interior points do not. -/
theorem corner_condition_of_boundary_sidon (m r s t : ℕ) [NeZero m]
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → ∃ B : Finset (ZMod m), IsSidon B ∧ B.card = r + 1) :
    r ≤ 5 ∨ s + t ≠ 0 := by
  by_cases hl : r ≤ 5
  · exact Or.inl hl
  have h6 : 6 ≤ r := by omega
  by_cases hs : s = 0
  · subst s
    obtain ⟨B, hB, hcard⟩ := hboundary h6 rfl
    exact corner_condition_of_sidon m r 0 t B hB (by simpa using hcard) hm hr
  · exact Or.inr (by omega)

/-- Numerical closure using Sidon only where the actual cut is maximal. -/
theorem small_gap_pos_of_boundary_sidon (m r s t : ℕ) [NeZero m]
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → ∃ B : Finset (ZMod m), IsSidon B ∧ B.card = r + 1) :
    0 < gap r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t) := by
  exact small_gap_pos r s t hr
    (corner_condition_of_boundary_sidon m r s t hm hr hboundary)

/-- The SO3 upper-bound interface now receives a boundary Sidon witness. -/
theorem scalar_lt_of_boundary_sidon (m r s t : ℕ) [NeZero m] (F : ℚ)
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → ∃ B : Finset (ZMod m), IsSidon B ∧ B.card = r + 1)
    (hupper : F ≤ upper r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t)) :
    F < (triangular r + t) * (volume ((r : ℚ) + 1 + s) (triangular r + t) + 1) := by
  exact scalar_lt_of_upper r s t F hr
    (corner_condition_of_boundary_sidon m r s t hm hr hboundary) hupper

/-- Direct interface from numerical Apéry-pair data, rather than assumed Sidonness.
Constructing this data from maximal Q2 is the remaining algebraic bridge. -/
theorem small_gap_pos_of_apery_pairs (S : AddSubmonoid ℕ) (m r s t : ℕ) [NeZero m]
    (hm : m = (r + 1 + s) + r * (r + 1) / 2 + t)
    (hr : 4 ≤ r ∧ r ≤ 8)
    (hboundary : 6 ≤ r → s = 0 → Nonempty (AperyPairData S m (r + 1))) :
    0 < gap r (cutoff r) ((r : ℚ) + 1 + s) (triangular r + t) := by
  apply small_gap_pos_of_boundary_sidon m r s t hm hr
  intro h6 hs
  obtain ⟨D⟩ := hboundary h6 hs
  exact ⟨D.residues, D.residues_sidon, D.residues_card⟩

end Ordinary.SmallScalar
end NSP14
