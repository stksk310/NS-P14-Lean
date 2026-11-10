module
public import NSP14.Homological.RegularElementQuotient
public import NSP14.Homological.FullListBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R σ : Type u) [Field k] [CommRing R] [Algebra k R] [Fintype σ]

noncomputable def scalarQuotientPolynomialModule (r : R) (φ : VariableRing k σ →ₐ[k] R) :
    ModuleCat.{u} (VariableRing k σ) :=
  (ModuleCat.restrictScalars φ.toRingHom).obj (scalarQuotientModule R r)

noncomputable def regularElementPolynomialReductionIso (r : R) (φ : VariableRing k σ →ₐ[k] R)
    (hr : Function.Injective (fun a : R => r*a)) (i : ℕ) :
    (regularPartialCoefficientComplex k R
      (r::(variableList k σ).map (fun x => φ (MvPolynomial.X x)))).homology i ≅
        koszulHomologyK k σ (scalarQuotientPolynomialModule k R σ r φ) i :=
  regularElementCoefficientReductionIso R r k _ hr i ≪≫
    coefficientComplexHomologyIso k (polynomialActionCoefficientIso k R σ φ (variableList k σ) (scalarQuotientModule R r)) i ≪≫
      coefficientCanonicalListHomologyIso k σ _ i

noncomputable def regularPartialPolynomialHomologyIso
    (φ : VariableRing k σ →ₐ[k] R) (xs : List σ) (hall : ∀ x,x∈xs) (hnodup : xs.Nodup) (i : ℕ) :
    (regularPartialCoefficientComplex k R (xs.map (fun x => φ (MvPolynomial.X x)))).homology i ≅
      koszulHomologyK k σ (polynomialRegularModule k σ R φ) i :=
  coefficientComplexHomologyIso k (regularPartialPolynomialIso k R σ φ xs) i ≪≫
    (fullListHomologyKIso k σ xs hall hnodup _ i).symm
end NSP14.Homological
