module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
@[expose] public section
open scoped Pointwise
namespace NSP14.Additive
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]
/-- Independent choices, including the empty sum. This is not a dilation image. -/
def iteratedSum (A : Finset G) : ℕ → Finset G
  | 0 => {0}
  | n+1 => iteratedSum A n + A
@[simp] theorem iteratedSum_zero (A : Finset G) : iteratedSum A 0 = {0} := rfl
@[simp] theorem iteratedSum_succ (A : Finset G) (n : ℕ) :
    iteratedSum A (n+1) = iteratedSum A n + A := rfl
@[simp] theorem iteratedSum_one (A : Finset G) : iteratedSum A 1 = A := by
  change (0 : Finset G) + A = A
  exact zero_add A
theorem iteratedSum_add (A : Finset G) (n m : ℕ) :
    iteratedSum A (n+m) = iteratedSum A n + iteratedSum A m := by
  induction m with
  | zero => exact (add_zero _).symm
  | succ m ih => simp only [Nat.add_succ, iteratedSum_succ, ih, add_assoc]
theorem iteratedSum_nonempty (A : Finset G) (hA : A.Nonempty) (n : ℕ) :
    (iteratedSum A n).Nonempty := by
  induction n with
  | zero => simp
  | succ n ih => exact Finset.add_nonempty.mpr ⟨ih,hA⟩
theorem iteratedSum_mono {A B : Finset G} (h : A ⊆ B) (n : ℕ) :
    iteratedSum A n ⊆ iteratedSum B n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Finset.add_subset_add ih h
theorem iteratedSum_subset_succ {A : Finset G} (h0 : 0 ∈ A) (n : ℕ) :
    iteratedSum A n ⊆ iteratedSum A (n+1) := by
  intro x hx
  exact Finset.mem_add.mpr ⟨x,hx,0,h0,add_zero x⟩
end NSP14.Additive
