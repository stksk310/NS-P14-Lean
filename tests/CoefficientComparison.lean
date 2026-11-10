module
public import NSP14
@[expose] public section
namespace CoefficientComparisonAcceptance
open NSP14.Target
theorem convolution (q n i : ℕ) :
    positiveOrdinaryCoefficient (q+n+1) i-positiveOrdinaryCoefficient (q+1) i =
      ∑ j ∈ Finset.range i, (q.choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target (q+1) n 1 (j+1) :=
  ordinary_difference_convolution q n i
theorem original_parameters (e d r i : ℕ) (hr : 1 ≤ r) (hre : r ≤ e) :
    positiveOrdinaryCoefficient (e+d) i-positiveOrdinaryCoefficient (e-r+1) i=
      ∑ j ∈ Finset.range i,((e-r).choose (i-(j+1)) : ℚ)*
        NSP14.Ordinary.TargetMargin.target e d r (j+1) :=
  ordinary_target_difference e d r i hr hre
theorem f_zero_correction (i : ℕ) (hi : 1 ≤ i) :
    positiveOrdinaryCoefficient 2 i-positiveOrdinaryCoefficient 1 i=((0 : ℕ).choose (i-1) : ℚ) := by
  simpa using ordinary_h0_correction 0 i hi
end CoefficientComparisonAcceptance
