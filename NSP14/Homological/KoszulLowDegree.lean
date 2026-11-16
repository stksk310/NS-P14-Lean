module

public import NSP14.Homological.KoszulFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

namespace NSP14.Homological

universe u v w
variable (R : Type u) [CommRing R]

/-- Zeroth homology as the actual cokernel of d₁, independently of finite-dimensionality. -/
noncomputable def chainH0QuotientEquiv (K : ChainComplex (ModuleCat.{w} R) ℕ) :
    K.homology 0 ≃ₗ[R] ((K.X 0) ⧸ (K.d 1 0).hom.range) :=
  ((ChainComplex.isoHomologyι₀ K) ≪≫
    (K.opcyclesIsoSc' 1 0 0 ((ComplexShape.down ℕ).prev_eq' rfl)
      ((ComplexShape.down ℕ).next_eq_self' 0 (by intro j hj; change j+1=0 at hj; omega))) ≪≫
    (K.sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

variable (k : Type u) (σ : Type v) [CommRing k]

noncomputable def koszulFirstProjection (x : σ) (xs : List σ)
    (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    (koszulList k σ (x::xs) M).X (i+1) ⟶ (koszulList k σ xs M).X i :=
  homotopyCofiber.fstX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (i+1) i rfl

noncomputable def koszulSecondProjection (x : σ) (xs : List σ)
    (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    (koszulList k σ (x::xs) M).X i ⟶ (koszulList k σ xs M).X i :=
  homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i

/-- The first signed block is -d, including the exterior sign convention. -/
theorem koszul_cons_d_first (x : σ) (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    (koszulList k σ (x::xs) M).d (i+2) (i+1) ≫ koszulFirstProjection k σ x xs M i =
      -koszulFirstProjection k σ x xs M (i+1) ≫ (koszulList k σ xs M).d (i+1) i :=
  homotopyCofiber.d_fstX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M))
    (i+2) (i+1) i rfl rfl

/-- The second signed block is the actual variable action plus d on the second summand. -/
theorem koszul_cons_d_second (x : σ) (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    (koszulList k σ (x::xs) M).d (i+1) i ≫ koszulSecondProjection k σ x xs M i =
      koszulFirstProjection k σ x xs M i ≫ ((MvPolynomial.X x : VariableRing k σ) • 𝟙 ((koszulList k σ xs M).X i)) +
        koszulSecondProjection k σ x xs M (i+1) ≫ (koszulList k σ xs M).d (i+1) i :=
  homotopyCofiber.d_sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M))
    (i+1) i rfl

noncomputable def koszulZeroDifferential (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    (koszulList k σ xs M).X 1 →ₗ[VariableRing k σ] M :=
  ((koszulZeroIso k σ xs M).hom).hom.comp ((koszulList k σ xs M).d 1 0).hom

/-- Natural identification with the actual boundary quotient in the original module. -/
noncomputable def koszulH0BoundaryEquiv (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    koszulHomology k σ xs M 0 ≃ₗ[VariableRing k σ] (M ⧸ (koszulZeroDifferential k σ xs M).range) :=
  (chainH0QuotientEquiv _ (koszulList k σ xs M)).trans
    (Submodule.Quotient.equiv _ _ (koszulZeroIso k σ xs M).toLinearEquiv (by
      rw [← LinearMap.range_comp]
      rfl))

end NSP14.Homological
