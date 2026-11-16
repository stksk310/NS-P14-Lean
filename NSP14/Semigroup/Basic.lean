module

public import NSP14.Combinatorics.Sidon
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace NSP14

/-- An actual cofinite additive submonoid of N. The conductor witness need not be least. -/
structure NumericalSemigroup where
  carrier : AddSubmonoid ℕ
  conductor : ℕ
  cofinite : ∀ n, conductor ≤ n → n ∈ carrier

instance : Membership ℕ NumericalSemigroup := ⟨fun S n => n ∈ S.carrier⟩

namespace NumericalSemigroup

variable (S : NumericalSemigroup)

theorem zero_mem : 0 ∈ S := S.carrier.zero_mem
theorem add_mem {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := S.carrier.add_mem hx hy

theorem multiple_mem (n : ℕ) {x : ℕ} (hx : x ∈ S) : n * x ∈ S := by
  change n * x ∈ S.carrier
  simpa [nsmul_eq_mul] using S.carrier.nsmul_mem hx n

theorem positive_exists : ∃ n : ℕ, 0 < n ∧ n ∈ S :=
  ⟨S.conductor + 1, by omega, S.cofinite _ (by omega)⟩

/-- The multiplicity is constructed as the least positive semigroup element. -/
noncomputable def multiplicity : ℕ := by
  classical
  exact Nat.find S.positive_exists

theorem multiplicity_spec : 0 < S.multiplicity ∧ S.multiplicity ∈ S := by
  classical
  exact Nat.find_spec S.positive_exists

theorem multiplicity_pos : 0 < S.multiplicity := S.multiplicity_spec.1
theorem multiplicity_mem : S.multiplicity ∈ S := S.multiplicity_spec.2

theorem multiplicity_le {x : ℕ} (hx : x ∈ S) (hpos : 0 < x) : S.multiplicity ≤ x := by
  classical
  exact Nat.find_min' S.positive_exists ⟨hpos, hx⟩

theorem multiplicity_eq {m : ℕ} (hm : 0 < m) (hmem : m ∈ S)
    (hmin : ∀ x ∈ S, 0 < x → m ≤ x) : S.multiplicity = m :=
  Nat.le_antisymm (S.multiplicity_le hmem hm) (hmin _ S.multiplicity_mem S.multiplicity_pos)

theorem multiplicity_le_conductor : S.multiplicity ≤ S.conductor + 1 :=
  S.multiplicity_le (S.cofinite _ (by omega)) (by omega)

/-- A positive multiple gives an explicit semigroup representative of every residue. -/
theorem residue_exists (r : Fin S.multiplicity) :
    ∃ x : ℕ, x ∈ S ∧ x % S.multiplicity = r.val := by
  have hm := S.multiplicity_pos
  have hmul : S.conductor ≤ S.conductor * S.multiplicity := by nlinarith
  refine ⟨S.conductor * S.multiplicity + r.val, S.cofinite _ (by omega), ?_⟩
  simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]

end NumericalSemigroup
end NSP14
