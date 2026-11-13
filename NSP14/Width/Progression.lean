module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
open scoped BigOperators
namespace NSP14.Width

/-- Twice a finite arithmetic progression, with all divisions cleared. -/
theorem progression_triangle (s k b : ℕ) :
    2*(∑ j∈Finset.range (k+1),(s*k+b-s*j))=s*k*(k+1)+2*b*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have he (j : ℕ) : s*(k+1)+b-s*(j+1)=s*k+b-s*j := by
      have h1 : s*(k+1)=s*k+s := by ring
      have h2 : s*(j+1)=s*j+s := by ring
      omega
    simp only [he,Nat.mul_zero,Nat.sub_zero]
    nlinarith only [ih]

/-- An arbitrary sufficiently long cutoff gives the same positive-part sum. -/
theorem progression_sum (d s k b N : ℕ) (_hs : 0<s) (hN : k<N)
    (hd : d=s*k+b) (hb : b<s) :
    2*(∑ j∈Finset.range N,(d-s*j))=s*k*(k+1)+2*b*(k+1) := by
  have he : (∑ j∈Finset.range N,(d-s*j))=
      ∑ j∈Finset.range (k+1),(d-s*j) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j hj hj'
      simp only [Finset.mem_range,not_lt] at hj hj'
      have hmul := Nat.mul_le_mul_left s hj'
      have : d<s*(k+1) := by nlinarith only [hd,hb]
      omega
  rw [he,hd]
  exact progression_triangle s k b

/-- The exact remainder correction in the Kneser volume bound, without rational division. -/
theorem progression_volume_identity (a s k b u B : ℕ)
    (hu : u=a+s*k+b) (hb : b<s) (hB : 2*(B-u)=s*k*(k+1)+2*b*(k+1)) (huB : u≤B) :
    2*s*B=2*s*u+(u-a)^2+s*(u-a)+b*(s-b) := by
  have hsub : u-a=s*k+b := by omega
  have hBu : B-u+u=B := Nat.sub_add_cancel huB
  have hdiff : s-b+b=s := Nat.sub_add_cancel (by omega)
  rw [hsub]
  nlinarith only [hB,hBu,hdiff]
end NSP14.Width
