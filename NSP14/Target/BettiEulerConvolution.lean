module
public import NSP14.Target.CoefficientComparison
@[expose] public section
open scoped BigOperators
namespace NSP14.Target

/-- Exact coefficient identity for beta_j=c_j+c_(j-1), with the
zeroth coefficient isolated explicitly. -/
theorem positive_euler_convolution_succ (f n : ℕ) (c : ℕ → ℚ) :
    (∑ j∈Finset.range (n+1),(f.choose ((n+1)-(j+1)) : ℚ)*(c (j+1)+c j))=
      (f.choose n : ℚ)*c 0+
        ∑ j∈Finset.range (n+1),((f+1).choose ((n+1)-(j+1)) : ℚ)*c (j+1) := by
  have hs : (∑ j∈Finset.range n,((f+1).choose (n-j) : ℚ)*c (j+1))=
      (∑ j∈Finset.range n,(f.choose (n-j) : ℚ)*c (j+1))+
        ∑ j∈Finset.range n,(f.choose (n-(j+1)) : ℚ)*c (j+1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have he : n-(j+1)+1=n-j := by have := Finset.mem_range.mp hj;omega
    have hp := Nat.choose_succ_succ f (n-(j+1))
    change (f+1).choose (n-(j+1)+1)=f.choose (n-(j+1))+f.choose (n-(j+1)+1) at hp
    rw [he] at hp
    have hq : ((f+1).choose (n-j) : ℚ)=(f.choose (n-(j+1)) : ℚ)+(f.choose (n-j) : ℚ) := by exact_mod_cast hp
    rw [hq]
    ring
  simp_rw [Nat.add_sub_add_right,mul_add]
  rw [Finset.sum_add_distrib,
    Finset.sum_range_succ (f:=fun j => (f.choose (n-j) : ℚ)*c (j+1)) n,
    Finset.sum_range_succ' (f:=fun j => (f.choose (n-j) : ℚ)*c j) n,
    Finset.sum_range_succ (f:=fun j => ((f+1).choose (n-j) : ℚ)*c (j+1)) n,hs]
  simp only [Nat.sub_self,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  ring

theorem positive_euler_convolution (f i : ℕ) (hi : 1 ≤ i) (c : ℕ → ℚ) :
    (∑ j∈Finset.range i,(f.choose (i-(j+1)) : ℚ)*(c (j+1)+c j))=
      (f.choose (i-1) : ℚ)*c 0+
        ∑ j∈Finset.range i,((f+1).choose (i-(j+1)) : ℚ)*c (j+1) := by
  cases i with
  | zero => omega
  | succ n => simpa only [Nat.add_sub_cancel] using positive_euler_convolution_succ f n c
end NSP14.Target
