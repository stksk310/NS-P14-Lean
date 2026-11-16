module
public import NSP14.Ordinary.TargetMargin
public import Mathlib.Data.Nat.Choose.Vandermonde
@[expose] public section
open scoped BigOperators
namespace NSP14.Target

/-- The positive-row coefficient only. Actual target Betti identification
is a separate theorem; this numerical definition does not assert it. -/
def positiveOrdinaryCoefficient (m i : ℕ) : ℚ := i*(m.choose (i+1) : ℚ)

private theorem vandermonde_shift (q n i : ℕ) (hi : 1 ≤ i) :
    ((q+n).choose (i-1) : ℚ) =
      ∑ j ∈ Finset.range i,(q.choose (i-(j+1)) : ℚ)*(n.choose j : ℚ) := by
  have h := Nat.add_choose_eq n q (i-1)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Nat.succ_eq_add_one] at h
  have he : i-1+1=i := by omega
  rw [he,Nat.add_comm n q] at h
  have h' : (q+n).choose (i-1)=∑ j ∈ Finset.range i,q.choose (i-(j+1))*n.choose j := by
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    have he' : i-1-j=i-(j+1) := by omega
    simp only [he',Nat.mul_comm]
  exact_mod_cast h'

/-- Target difference as the exact convolution against the pre-existing R_j.
All differences take place in Q, with no truncated natural subtraction.
The zeroth row cancels and hence is included as the empty convolution. -/
theorem ordinary_difference_convolution (q n i : ℕ) :
    positiveOrdinaryCoefficient (q+n+1) i-positiveOrdinaryCoefficient (q+1) i =
      ∑ j ∈ Finset.range i,(q.choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target (q+1) n 1 (j+1) := by
  by_cases hi : i=0
  · subst i
    simp [positiveOrdinaryCoefficient]
  have hi' : 1 ≤ i := by omega
  induction n with
  | zero =>
    simp only [Nat.add_zero,sub_self]
    symm
    apply Finset.sum_eq_zero
    intro j _
    simp [NSP14.Ordinary.TargetMargin.target,Nat.choose_eq_zero_of_lt (by omega : 0 < j+1),
      Nat.choose_eq_zero_of_lt (by omega : 0 < j+1+1)]
  | succ n ih =>
    have hs : (∑ j ∈ Finset.range i,(q.choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target (q+1) (n+1) 1 (j+1)) =
        (∑ j ∈ Finset.range i,(q.choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target (q+1) n 1 (j+1))+
        (q+n+1 : ℕ)*((q+n).choose (i-1) : ℚ) := by
      rw [vandermonde_shift q n i hi',Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have h := NSP14.Ordinary.TargetMargin.target_step (q+1) n 1 (j+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h ⊢
      have ht : NSP14.Ordinary.TargetMargin.target (q+1) (n+1) 1 (j+1)=
          NSP14.Ordinary.TargetMargin.target (q+1) n 1 (j+1)+
          ((q : ℚ)+n+1)*(n.choose j : ℚ) := by linarith
      rw [ht]
      ring
    have hb := Nat.add_one_mul_choose_eq (q+n) (i-1)
    have he : i-1+1=i := by omega
    rw [he] at hb
    have hb' : ((q+n+1 : ℕ) : ℚ)*((q+n).choose (i-1) : ℚ)=
        ((q+n+1).choose i : ℚ)*(i : ℚ) := by exact_mod_cast hb
    have hp : positiveOrdinaryCoefficient (q+(n+1)+1) i-
        positiveOrdinaryCoefficient (q+n+1) i=
        (q+n+1 : ℕ)*((q+n).choose (i-1) : ℚ) := by
      unfold positiveOrdinaryCoefficient
      have hc := Nat.choose_succ_succ (q+n+1) i
      have hn : q+(n+1)+1=(q+n+1)+1 := by omega
      rw [hn]
      have hq : (((q+n+1)+1).choose (i+1) : ℚ)=
          ((q+n+1).choose i : ℚ)+((q+n+1).choose (i+1) : ℚ) := by exact_mod_cast hc
      rw [hq]
      nlinarith
    rw [hs,← ih]
    linarith

/-- The coefficient of the H0 correction (f+1) z (1+z)^f.
It applies only to positive rows; the actual zeroth coefficient cancels. -/
theorem ordinary_h0_correction (f i : ℕ) (hi : 1 ≤ i) :
    positiveOrdinaryCoefficient (f+2) i-positiveOrdinaryCoefficient (f+1) i=
      (f+1 : ℕ)*(f.choose (i-1) : ℚ) := by
  unfold positiveOrdinaryCoefficient
  have hp := Nat.choose_succ_succ (f+1) i
  have hb := Nat.add_one_mul_choose_eq f (i-1)
  rw [Nat.sub_add_cancel hi] at hb
  have hp' : ((f+2).choose (i+1) : ℚ)=
      ((f+1).choose i : ℚ)+((f+1).choose (i+1) : ℚ) := by exact_mod_cast hp
  have hb' : ((f+1 : ℕ) : ℚ)*(f.choose (i-1) : ℚ)=
      ((f+1).choose i : ℚ)*(i : ℚ) := by exact_mod_cast hb
  rw [hp']
  nlinarith

/-- The exact convolution with the original e,d,r parametrization.
The final capacity has m=e+d variables, whereas the base term has e-r+1. -/
theorem ordinary_target_difference (e d r i : ℕ) (hr : 1 ≤ r) (hre : r ≤ e) :
    positiveOrdinaryCoefficient (e+d) i-positiveOrdinaryCoefficient (e-r+1) i=
      ∑ j ∈ Finset.range i,((e-r).choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target e d r (j+1) := by
  have h := ordinary_difference_convolution (e-r) (d+r-1) i
  have hm : (e-r)+(d+r-1)+1=e+d := by omega
  rw [hm] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold NSP14.Ordinary.TargetMargin.target
  have hn : d+r-1+1-1=d+r-1 := by omega
  have heq : (((e-r+1 : ℕ) : ℚ)-1+(j+1 : ℕ))=(e : ℚ)-r+(j+1 : ℕ) := by
    rw [Nat.cast_add,Nat.cast_sub hre,Nat.cast_one]
    ring
  rw [hn]
  simp only [Nat.cast_one,heq]

/-- Extra convolution terms beyond the relative rank can be retained and
then discarded by nonnegativity, rather than hidden by natural truncation. -/
theorem targetCoefficient_nonneg (e d r j : ℕ) (hre : r ≤ e) :
    0 ≤ NSP14.Ordinary.TargetMargin.target e d r j := by
  unfold NSP14.Ordinary.TargetMargin.target
  have h : (r : ℚ) ≤ e := by exact_mod_cast hre
  apply add_nonneg
  · apply mul_nonneg
    · have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      linarith
    · positivity
  · positivity
end NSP14.Target
