module
public import NSP14.Homological.RankEuler
public import NSP14.Homological.KoszulRanks
public import NSP14.Homological.FreeKoszulHomology
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- Partial alternating sum of actual ordinary Tor ranks over the specified
polynomial ring. The variable type is part of the definition. -/
noncomputable def bettiEuler (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (j : ℕ) : ℤ :=
  partialEuler (totalBetti k σ M) j

@[simp] theorem bettiEuler_zero (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] : bettiEuler k σ M 0=(totalBetti k σ M 0 : ℤ) := rfl

theorem bettiEuler_succ (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (j : ℕ) :
    bettiEuler k σ M (j+1)=(totalBetti k σ M (j+1) : ℤ)-bettiEuler k σ M j := rfl

/-- A free polynomial module is the guard against an unjustified universal
nonnegativity claim for reversed partial Euler sums. -/
theorem bettiEuler_free_one :
    bettiEuler k σ (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 1 = -1 := by
  rw [show 1=0+1 by rfl,bettiEuler_succ,bettiEuler_zero,
    totalBetti_free_succ,totalBetti_free_zero]
  norm_num

variable (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
variable [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃]

omit [Module.Finite (VariableRing k σ) S.X₁] [Module.Finite (VariableRing k σ) S.X₂] in
theorem koszulCorrectionRank_le (hS : S.ShortExact) (j : ℕ) :
    koszulCorrectionRank k σ S hS j ≤ totalBetti k σ S.X₃ (j+1) := by
  have h := ((coefficientKoszulSequence_shortExact k σ S hS).δ (j+1) j rfl).hom.finrank_range_le
  change koszulCorrectionRank k σ S hS j ≤
    Module.finrank k ((coefficientKoszulComplex k σ S.X₃).homology (j+1)) at h
  rw [(coefficientKoszulHomologyIso k σ S.X₃ (j+1)).toLinearEquiv.finrank_eq] at h
  exact h

/-- The actual connecting rank telescopes, including the special H₀ term. -/
theorem bettiEuler_shortExact (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₂ j = bettiEuler k σ S.X₁ j + bettiEuler k σ S.X₃ j -
      (koszulCorrectionRank k σ S hS j : ℤ) := by
  induction j with
  | zero =>
    have h := koszul_betti_rank_correction_zero k σ S hS
    simp only [bettiEuler_zero]
    omega
  | succ j ih =>
    have h := koszul_betti_rank_correction k σ S hS j
    simp only [bettiEuler_succ]
    omega

/-- The second identity subtracts the complement of the connecting rank,
which is distinct from the correction rank in the preceding identity. -/
theorem bettiEuler_kernel (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₁ j = bettiEuler k σ S.X₂ j + bettiEuler k σ S.X₃ (j+1) -
      ((totalBetti k σ S.X₃ (j+1) : ℤ)-(koszulCorrectionRank k σ S hS j : ℤ)) := by
  rw [bettiEuler_shortExact k σ S hS j,bettiEuler_succ]
  ring

theorem bettiEuler_middle_le (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₂ j ≤ bettiEuler k σ S.X₁ j + bettiEuler k σ S.X₃ j := by
  rw [bettiEuler_shortExact k σ S hS j]
  omega

theorem bettiEuler_kernel_le (hS : S.ShortExact) (j : ℕ) :
    bettiEuler k σ S.X₁ j ≤ bettiEuler k σ S.X₂ j + bettiEuler k σ S.X₃ (j+1) := by
  rw [bettiEuler_kernel k σ S hS j]
  have h := koszulCorrectionRank_le k σ S hS j
  omega
end NSP14.Homological
