module
public import NSP14.Homological.HankelAction
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] (d u j n : ℕ)

theorem hankel_delta_upper (g : Fin u → k) (b : Fin u) :
    (hankelAction k d u j ((fun a => if n=d-1-a.val then (1:k) else 0),g)).2 b=
      if n<d ∧ j+n+1=d+b.val then 1 else 0 := by
  change (∑ a : Fin d,(if j=a.val+b.val then (1:k) else 0)*
    (if n=d-1-a.val then (1:k) else 0))=_
  by_cases hn : n<d
  · let a0 : Fin d := ⟨d-1-n,by omega⟩
    have ha0 : n=d-1-a0.val := by dsimp [a0];omega
    rw [Fintype.sum_eq_single a0]
    · rw [ite_eq_left ha0,mul_one]
      have he : (j=a0.val+b.val) ↔ (j+n+1=d+b.val) := by dsimp [a0];omega
      simp only [hn,true_and,he]
    · intro a hne
      have hna : n≠d-1-a.val := by
        intro he
        apply hne
        apply Fin.ext
        have ha := a.isLt
        change a.val=d-1-n
        omega
      rw [ite_eq_right hna,mul_zero]
  · rw [ite_eq_right (by omega)]
    apply Finset.sum_eq_zero
    intro a _
    have hna : n≠d-1-a.val := by have := a.isLt;omega
    rw [ite_eq_right hna,mul_zero]
end NSP14.Homological
