module

public import NSP14.Homological.PolynomialBaseChangeModule
public import NSP14.Homological.ModuleProducts
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]

noncomputable def koszulChainCoefficientZeroIso (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ)) :
    coefficientModule k σ ((koszulList k σ xs M).X 0) ≅ coefficientModule k σ M :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso (koszulZeroIso k σ xs M)

noncomputable def koszulChainCoefficientSuccIso (x : σ) (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    coefficientModule k σ ((koszulList k σ (x::xs) M).X (i+1)) ≅
      ModuleCat.of k (coefficientModule k σ ((koszulList k σ xs M).X i) ×
        coefficientModule k σ ((koszulList k σ xs M).X (i+1))) :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
    (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i).toModuleIso

theorem koszul_chain_coefficient_finite (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite k (coefficientModule k σ M)] (i : ℕ) :
    Module.Finite k (coefficientModule k σ ((koszulList k σ xs M).X i)) := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => exact inferInstanceAs (Module.Finite k (coefficientModule k σ M))
    | succ i =>
      have : Subsingleton (coefficientModule k σ ((koszulList k σ [] M).X (i+1))) :=
        (show Subsingleton ((koszulList k σ [] M).X (i+1)) from ModuleCat.subsingleton_of_isZero
          (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp)))
      infer_instance
  | cons x xs ih =>
    cases i with
    | zero => exact Module.Finite.equiv (koszulChainCoefficientZeroIso k σ (x::xs) M).symm.toLinearEquiv
    | succ i =>
      let : Module.Finite k (coefficientModule k σ ((koszulList k σ xs M).X i)) := ih i
      let : Module.Finite k (coefficientModule k σ ((koszulList k σ xs M).X (i+1))) := ih (i+1)
      exact Module.Finite.equiv
        (M := coefficientModule k σ ((koszulList k σ xs M).X i) ×
          coefficientModule k σ ((koszulList k σ xs M).X (i+1)))
        (koszulChainCoefficientSuccIso k σ x xs M i).symm.toLinearEquiv

/-- This chain-dimension formula explicitly requires M to be finite over k.
It is never used to assert that the chains of actual G are finite over k. -/
theorem koszul_chain_finrank (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite k (coefficientModule k σ M)] (i : ℕ) :
    Module.finrank k (coefficientModule k σ ((koszulList k σ xs M).X i)) =
      Module.finrank k (coefficientModule k σ M) * Nat.choose xs.length i := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero =>
      rw [(koszulChainCoefficientZeroIso k σ [] M).toLinearEquiv.finrank_eq]
      simp
    | succ i =>
      have : Subsingleton (coefficientModule k σ ((koszulList k σ [] M).X (i+1))) :=
        (show Subsingleton ((koszulList k σ [] M).X (i+1)) from ModuleCat.subsingleton_of_isZero
          (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp)))
      simp [Module.finrank_zero_of_subsingleton]
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [(koszulChainCoefficientZeroIso k σ (x::xs) M).toLinearEquiv.finrank_eq]
      simp
    | succ i =>
      let : Module.Finite k (coefficientModule k σ ((koszulList k σ xs M).X i)) :=
        koszul_chain_coefficient_finite k σ xs M i
      let : Module.Finite k (coefficientModule k σ ((koszulList k σ xs M).X (i+1))) :=
        koszul_chain_coefficient_finite k σ xs M (i+1)
      rw [(koszulChainCoefficientSuccIso k σ x xs M i).toLinearEquiv.finrank_eq]
      change Module.finrank k (coefficientModule k σ ((koszulList k σ xs M).X i) ×
        coefficientModule k σ ((koszulList k σ xs M).X (i+1))) = _
      rw [Module.finrank_prod,ih,ih]
      simp only [List.length_cons,Nat.choose_succ_succ,Nat.mul_add]

end NSP14.Homological
