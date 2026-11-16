module
public import NSP14.Homological.PascalBound
@[expose] public section
open scoped BigOperators
namespace NSP14.Homological

theorem binomialTransform_positive (f : ℕ) (b : ℕ → ℕ) (i : ℕ) :
    binomialTransform f (fun j => if j=0 then 0 else b j) i=
      ∑ j∈Finset.range i,f.choose (i-(j+1))*b (j+1) := by
  unfold binomialTransform
  rw [Finset.sum_range_succ']
  simp
end NSP14.Homological
