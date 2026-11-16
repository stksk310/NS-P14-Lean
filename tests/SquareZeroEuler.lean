module
public import NSP14
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14.Homological
namespace SquareZeroAcceptance
abbrev k := ZMod 2
noncomputable abbrev M := firstOrderModule k 2 3

theorem actual_rank_two_boundary : koszulBoundaryRank k (Fin 2) M 2=1 := by
  have h := firstOrder_boundaryRank k 2 3 1
  norm_num at h
  exact h

theorem H0_generators : bettiEuler k (Fin 2) M 0=4 := by
  have h := firstOrder_Euler k 2 3 (by decide) 0
  norm_num at h
  exact h

theorem first_row : bettiEuler k (Fin 2) M 1=5 := by
  have h := firstOrder_Euler k 2 3 (by decide) 1
  norm_num at h
  exact h

theorem top_and_above (j : ℕ) (hj : 2 ≤ j) : bettiEuler k (Fin 2) M j=0 :=
  finite_koszul_bettiEuler_eq_zero_of_ge k (Fin 2) M (by decide) j (by simpa using hj)
end SquareZeroAcceptance
