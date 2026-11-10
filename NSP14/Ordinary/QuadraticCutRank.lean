module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Order.Monotone.Basic

@[expose] public section

namespace NSP14.Ordinary

/-- Integer triangular function used by the Green degree-two decomposition. -/
def quadraticTriangular (p : ℕ) : ℕ := (p + 1).choose 2

@[simp] theorem quadraticTriangular_zero : quadraticTriangular 0 = 0 := rfl

theorem quadraticTriangular_succ (p : ℕ) :
    quadraticTriangular (p + 1) = quadraticTriangular p + p + 1 := by
  unfold quadraticTriangular
  rw [Nat.choose_succ_succ']
  change (p + 1).choose 1 + (p + 1).choose 2 = (p + 1).choose 2 + p + 1
  rw [Nat.choose_one_right]
  omega

theorem quadraticTriangular_ge (p : ℕ) : p ≤ quadraticTriangular p := by
  induction p with
  | zero => simp
  | succ p ih => rw [quadraticTriangular_succ]; omega

theorem quadraticTriangular_strictMono : StrictMono quadraticTriangular := by
  apply strictMono_nat_of_lt_succ
  intro p
  rw [quadraticTriangular_succ]
  omega

/-- Canonical integer p. This is arithmetic only, not a Green or cut-existence theorem. -/
def quadraticIndex (a : ℕ) : ℕ := Nat.findGreatest (fun p => quadraticTriangular p ≤ a) (a + 1)

theorem quadraticIndex_lower (a : ℕ) : quadraticTriangular (quadraticIndex a) ≤ a :=
  Nat.findGreatest_spec (P := fun p => quadraticTriangular p ≤ a)
    (m := 0) (Nat.zero_le _) (Nat.zero_le a)

theorem quadraticIndex_le (a : ℕ) : quadraticIndex a ≤ a :=
  (quadraticTriangular_ge _).trans (quadraticIndex_lower a)

theorem quadraticIndex_upper (a : ℕ) : a < quadraticTriangular (quadraticIndex a + 1) := by
  by_contra hn
  have hle := Nat.le_findGreatest (P := fun p => quadraticTriangular p ≤ a)
    (show quadraticIndex a + 1 ≤ a + 1 by have := quadraticIndex_le a; omega)
    (show quadraticTriangular (quadraticIndex a + 1) ≤ a by omega)
  change quadraticIndex a + 1 ≤ quadraticIndex a at hle
  omega

theorem quadratic_decomposition (a : ℕ) :
    a = quadraticTriangular (quadraticIndex a) + (a - quadraticTriangular (quadraticIndex a)) ∧
      a - quadraticTriangular (quadraticIndex a) ≤ quadraticIndex a := by
  have hl := quadraticIndex_lower a
  have hu := quadraticIndex_upper a
  rw [quadraticTriangular_succ] at hu
  omega

/-- The prescribed r=max(2,p); no triangular lower bound is asserted at r=2. -/
def quadraticCutRank (a : ℕ) : ℕ := max 2 (quadraticIndex a)

theorem quadraticCutRank_two_le (a : ℕ) : 2 ≤ quadraticCutRank a := le_max_left _ _

theorem quadraticCutRank_eq_index {a : ℕ} (hr : 3 ≤ quadraticCutRank a) :
    quadraticCutRank a = quadraticIndex a := by
  unfold quadraticCutRank at hr ⊢
  omega

theorem quadraticCutRank_triangular {a : ℕ} (hr : 3 ≤ quadraticCutRank a) :
    quadraticTriangular (quadraticCutRank a) ≤ a := by
  rw [quadraticCutRank_eq_index hr]
  exact quadraticIndex_lower a

theorem quadraticIndex_le_of_bound {a n : ℕ} (ha : a ≤ quadraticTriangular n) :
    quadraticIndex a ≤ n := by
  have hl := quadraticIndex_lower a
  by_contra hn
  have hlt := quadraticTriangular_strictMono (show n < quadraticIndex a by omega)
  omega

theorem quadraticCutRank_le_of_bound {a n : ℕ} (hn : 2 ≤ n)
    (ha : a ≤ quadraticTriangular n) : quadraticCutRank a ≤ n :=
  max_le hn (quadraticIndex_le_of_bound ha)

theorem quadraticCutRank_maximal {a n : ℕ} (ha : a ≤ quadraticTriangular n)
    (hr : 3 ≤ quadraticCutRank a) (hn : quadraticCutRank a = n) :
    a = quadraticTriangular n := by
  have hl := quadraticCutRank_triangular hr
  rw [hn] at hl
  omega

end NSP14.Ordinary
