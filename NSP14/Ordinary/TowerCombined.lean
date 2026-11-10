module
public import NSP14.Ordinary.TowerTerminal
public import NSP14.Ordinary.JumpEuler
public import NSP14.Ordinary.TowerH0
public import NSP14.Ordinary.TowerHarmonic
@[expose] public section
open scoped BigOperators
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem cutHighEuler_shift_sum (n j : ℕ) :
    C.cutHighEuler 2 2 j+∑ t ∈ Finset.range n,C.cutHighEuler (3+t) (3+t) j=
      (∑ t ∈ Finset.range n,C.cutHighEuler (2+t) (2+t) j)+C.cutHighEuler (2+n) (2+n) j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have he : 3+n=2+(n+1) := by omega
    rw [he]
    omega

/-- The second and third actual Tor inequalities telescope on the same
tower. The last X is proved zero; it is not discarded by an assumed cutoff. -/
theorem cutTower_combined (j : ℕ) :
    C.cutHighEuler 2 2 (j+1)+C.cutTEuler j ≤
      ∑ t ∈ Finset.range (S.qTopDegree-1),
        (C.cutHighEuler (2+t) (2+t) (j+1)+C.cutHighEuler (2+t) (3+t) j) := by
  have ht := C.cutTEuler_le_sum j
  have hk := Finset.sum_le_sum (s:=Finset.range (S.qTopDegree-1))
    (fun t _ => C.cutTower_kernel_le (2+t) (by omega) j)
  have hz := C.cutHighEuler_eq_zero_of_top_lt (2+(S.qTopDegree-1)) (2+(S.qTopDegree-1)) (j+1)
    (by omega) (by omega)
  have he := C.cutHighEuler_shift_sum (S.qTopDegree-1) (j+1)
  simp only [Finset.sum_add_distrib] at hk ⊢
  have hnat (t : ℕ) : 2+t+1=3+t := by omega
  simp_rw [hnat] at hk
  rw [hz,add_zero] at he
  omega
end NSP14.NumericalSemigroup.LinearCutData
