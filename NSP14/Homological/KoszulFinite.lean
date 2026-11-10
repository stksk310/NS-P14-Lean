module

public import NSP14.Homological.KoszulNaturality
public import NSP14.Homological.PolynomialModules
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u v w
variable (k : Type u) (σ : Type v) [CommRing k]

/-- The zeroth chain group is the original module, for the actual subset-recursive complex. -/
noncomputable def koszulZeroIso (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    (koszulList k σ xs M).X 0 ≅ M :=
  match xs with
  | [] => Iso.refl _
  | x::xs => (HomologicalComplex.homotopyCofiber.XIso
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 (by
        intro h
        change (ComplexShape.down ℕ).next 0+1=0 at h
        omega)) ≪≫ koszulZeroIso xs M

/-- Finite generation is over the polynomial ring, with no finite k-chain-group hypothesis. -/
theorem koszul_chain_finite (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.Finite (VariableRing k σ) ((koszulList k σ xs M).X i) := by
  induction xs generalizing i with
  | nil =>
    by_cases hi : i=0
    · subst i
      exact inferInstanceAs (Module.Finite (VariableRing k σ) M)
    · have : Subsingleton ((koszulList k σ [] M).X i) :=
        ModuleCat.subsingleton_of_isZero (koszul_piece_isZero_of_gt k σ [] M i (by simp; omega))
      infer_instance
  | cons x xs ih =>
    cases i with
    | zero =>
      have := ih 0
      let e := (koszulZeroIso k σ (x::xs) M) ≪≫ (koszulZeroIso k σ xs M).symm
      exact Module.Finite.equiv e.symm.toLinearEquiv
    | succ i =>
      let : Module.Finite (VariableRing k σ) ((koszulList k σ xs M).X i) := ih i
      let : Module.Finite (VariableRing k σ) ((koszulList k σ xs M).X (i+1)) := ih (i+1)
      let e := (koszulConsPieceIso k σ x xs M i) ≪≫ ModuleCat.biprodIsoProd _ _
      exact Module.Finite.equiv
        (M := (koszulList k σ xs M).X i × (koszulList k σ xs M).X (i+1)) e.symm.toLinearEquiv

/-- Kernel/image homology agrees with mathlib's abstract homology, before dimension is used. -/
noncomputable def koszulHomologyQuotientIso (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    koszulHomology k σ xs M i ≅ ((koszulList k σ xs M).sc i).moduleCatLeftHomologyData.H :=
  ((koszulList k σ xs M).sc i).moduleCatHomologyIso

/-- Noetherianity yields finite polynomial-module homology; k-finiteness still needs annihilation. -/
theorem koszul_homology_polynomial_finite [IsNoetherianRing k] [Finite σ]
    (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.Finite (VariableRing k σ) (koszulHomology k σ xs M i) := by
  have hchain := koszul_chain_finite k σ xs M i
  let e := koszulHomologyQuotientIso k σ xs M i
  have : Module.Finite (VariableRing k σ) ((koszulList k σ xs M).sc i).moduleCatLeftHomologyData.H := by
    have : Module.Finite (VariableRing k σ) (((koszulList k σ xs M).sc i).g.hom.ker) := by
      change Module.Finite (VariableRing k σ) ((koszulList k σ xs M).d i ((ComplexShape.down ℕ).next i)).hom.ker
      infer_instance
    exact Module.Finite.of_surjective
      (((koszulList k σ xs M).sc i).moduleCatToCycles.range.mkQ) (Submodule.mkQ_surjective _)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end NSP14.Homological
