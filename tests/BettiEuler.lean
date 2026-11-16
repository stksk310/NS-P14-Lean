module
public import NSP14
@[expose] public section
open CategoryTheory NSP14.Homological
namespace BettiEulerAcceptance
variable (k σ : Type) [Field k] [Fintype σ]
variable (S : ShortComplex (ModuleCat (VariableRing k σ)))
variable [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃]

theorem actual_les_correction (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₂ j = bettiEuler k σ S.X₁ j + bettiEuler k σ S.X₃ j -
      (koszulCorrectionRank k σ S hS j : ℤ) :=
  bettiEuler_shortExact k σ S hS j

theorem actual_les_complement (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₁ j ≤ bettiEuler k σ S.X₂ j + bettiEuler k σ S.X₃ (j+1) :=
  bettiEuler_kernel_le k σ S hS j
end BettiEulerAcceptance
