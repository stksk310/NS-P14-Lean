module
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
@[expose] public section
open scoped BigOperators
namespace NSP14.Homological

def pascalStep (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => b 0
  | i+1 => b (i+1)+b i

def pascalIter (b : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => b
  | n+1 => pascalStep (pascalIter b n)

theorem pascalStep_mono {a b : ℕ → ℕ} (h : ∀ i,a i≤b i) : ∀ i,pascalStep a i≤pascalStep b i := by
  intro i
  cases i with
  | zero => exact h 0
  | succ i => exact Nat.add_le_add (h (i+1)) (h i)

def binomialTransform (n : ℕ) (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ j∈Finset.range (i+1),n.choose (i-j)*b j

theorem binomialTransform_at_zero (n : ℕ) (b : ℕ → ℕ) : binomialTransform n b 0=b 0 := by
  simp [binomialTransform]

theorem binomialTransform_rank_zero (b : ℕ → ℕ) (i : ℕ) : binomialTransform 0 b i=b i := by
  unfold binomialTransform
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hle : j≤i := by have := Finset.mem_range.mp hj;omega
    have hpos : 0<i-j := by omega
    rw [Nat.choose_eq_zero_of_lt hpos,zero_mul]
  · simp

theorem binomialTransform_succ (n : ℕ) (b : ℕ → ℕ) (i : ℕ) :
    binomialTransform (n+1) b (i+1)=binomialTransform n b (i+1)+binomialTransform n b i := by
  have hs : (∑ j∈Finset.range (i+1),(n+1).choose (i+1-j)*b j)=
      (∑ j∈Finset.range (i+1),n.choose (i+1-j)*b j)+
        ∑ j∈Finset.range (i+1),n.choose (i-j)*b j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have he : i+1-j=(i-j)+1 := by have := Finset.mem_range.mp hj;omega
    rw [he,Nat.choose_succ_succ]
    ring
  unfold binomialTransform
  rw [Finset.sum_range_succ (f:=fun j => (n+1).choose (i+1-j)*b j) (i+1),
    Finset.sum_range_succ (f:=fun j => n.choose (i+1-j)*b j) (i+1),hs]
  simp only [Nat.sub_self,Nat.choose_zero_right,one_mul]
  omega

theorem pascalIter_eq_binomialTransform (b : ℕ → ℕ) (n i : ℕ) :
    pascalIter b n i=binomialTransform n b i := by
  induction n generalizing i with
  | zero => exact (binomialTransform_rank_zero b i).symm
  | succ n ih =>
    cases i with
    | zero => simp only [pascalIter,pascalStep,ih,binomialTransform_at_zero]
    | succ i =>
      change pascalIter b n (i+1)+pascalIter b n i=_
      rw [ih,ih,binomialTransform_succ]
end NSP14.Homological
