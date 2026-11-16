module
public import NSP14.Width.DensePayment
@[expose] public section
namespace NSP14.Tests.DensePayment

theorem q4_t2 (j : ℕ) (hj : j≤5) :
    (j+1)*(5:ℕ).choose (j+2)+9*(4:ℕ).choose j+2*(3:ℕ).choose j≤(j+1)*(7:ℕ).choose (j+2) := by
  simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,zero_mul,add_zero] using
    Width.dense_payment 4 2 9 0 2 j (by decide) (by decide) (by decide) hj (by decide) (by decide)
      (by decide) (by decide) (by decide)
theorem q4_t3 (j : ℕ) (hj : j≤5) :
    (j+1)*(5:ℕ).choose (j+2)+11*(4:ℕ).choose j+3*(5:ℕ).choose j+4*(3:ℕ).choose j≤(j+1)*(8:ℕ).choose (j+2) := by
  exact Width.dense_payment 4 3 11 3 4 j (by decide) (by decide) (by decide) hj (by decide) (by decide)
    (by decide) (by decide) (by decide)
theorem q4_t4 (j : ℕ) (hj : j≤5) :
    (j+1)*(5:ℕ).choose (j+2)+13*(4:ℕ).choose j+4*(5:ℕ).choose j+8*(3:ℕ).choose j≤(j+1)*(9:ℕ).choose (j+2) := by
  exact Width.dense_payment 4 4 13 4 8 j (by decide) (by decide) (by decide) hj (by decide) (by decide)
    (by decide) (by decide) (by decide)
end NSP14.Tests.DensePayment
