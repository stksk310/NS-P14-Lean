module

import NSP14

open NSP14

namespace NSP14.Block02Audit

-- A concrete additive submonoid, S = <3,4>, supplies nontrivial valid pair data.
private def exampleMonoid : AddSubmonoid ℕ where
  carrier := {n | ∃ a b : ℕ, n = 3 * a + 4 * b}
  zero_mem' := ⟨0, 0, by omega⟩
  add_mem' := by
    rintro x y ⟨a, b, hx⟩ ⟨c, d, hy⟩
    exact ⟨a + c, b + d, by omega⟩

private theorem min_zero : IsAperyMin exampleMonoid 3 0 := by
  constructor
  · exact ⟨0, 0, by omega⟩
  · intro y hy h
    omega

private theorem min_four : IsAperyMin exampleMonoid 3 4 := by
  constructor
  · exact ⟨0, 1, by omega⟩
  · rintro y ⟨a, b, hy⟩ h
    omega

private theorem min_eight : IsAperyMin exampleMonoid 3 8 := by
  constructor
  · exact ⟨0, 2, by omega⟩
  · rintro y ⟨a, b, hy⟩ h
    omega

private def exampleValue (i : Fin 2) : ℕ := 4 * i.val

private def exampleData : AperyPairData exampleMonoid 3 2 where
  value := exampleValue
  injective_value := by
    intro i j h
    apply Fin.ext
    dsimp [exampleValue] at h
    omega
  value_min := by
    intro i
    have h : exampleValue i = 0 ∨ exampleValue i = 4 := by
      dsimp [exampleValue]
      omega
    rcases h with h | h
    · rw [h]; exact min_zero
    · rw [h]; exact min_four
  pair_min := by
    intro i j
    have h : exampleValue i + exampleValue j = 0 ∨
        exampleValue i + exampleValue j = 4 ∨
        exampleValue i + exampleValue j = 8 := by
      dsimp [exampleValue]
      omega
    rcases h with h | h | h
    · rw [h]; exact min_zero
    · rw [h]; exact min_four
    · rw [h]; exact min_eight
  pair_unique := by decide

-- The bridge has a satisfiable nontrivial input, including repeated pairs.
example : exampleData.residues.card = 2 := exampleData.residues_card
example : IsSidon exampleData.residues := exampleData.residues_sidon
example : 2 * (2 - 1) + 1 ≤ 3 := exampleData.multiplicity_bound
example : (2 - 1) ^ 2 ≤ 1 := exampleData.deficit_bound 1 (by decide) (by decide)

-- The smallest permitted modulus admits a singleton strong Sidon set.
example : IsSidon ({0} : Finset (ZMod 1)) := by unfold IsSidon; decide

-- The Nat division used for m agrees with the rational triangular term in the gap.
example (r : ℕ) (hr : 4 ≤ r ∧ r ≤ 8) :
    ((r * (r + 1) / 2 : ℕ) : ℚ) = Ordinary.SmallScalar.triangular r := by
  obtain ⟨hlo, hhi⟩ := hr
  interval_cases r <;> norm_num [Ordinary.SmallScalar.triangular]

private theorem top_min (m x : ℕ) (hx : x < m) :
    IsAperyMin (⊤ : AddSubmonoid ℕ) m x := by
  constructor
  · simp
  · intro y _ h
    rw [Nat.mod_eq_of_lt hx] at h
    have hy := Nat.mod_le y m
    omega

-- Without pair_min, minimal individual representatives and unique numeric sums
-- do not imply Sidon residues: 1+1 wraps to the same residue as 0+0 mod 2.
example (i : Fin 2) : IsAperyMin (⊤ : AddSubmonoid ℕ) 2 i.val :=
  top_min 2 i.val i.isLt
example : ∀ i j k l : Fin 2, i.val + j.val = k.val + l.val →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide
example : ¬IsAperyMin (⊤ : AddSubmonoid ℕ) 2 2 := by
  intro h
  have hh := h.2 0 (by simp) (by norm_num)
  omega
example : ¬IsSidon ({0, 1} : Finset (ZMod 2)) := by unfold IsSidon; decide

-- Without pair_unique, even all pair sums being minimal is insufficient.
example (i j : Fin 3) : IsAperyMin (⊤ : AddSubmonoid ℕ) 5 (i.val + j.val) :=
  top_min 5 (i.val + j.val) (by omega)
example : ¬IsSidon ({0, 1, 2} : Finset (ZMod 5)) := by unfold IsSidon; decide

end NSP14.Block02Audit
