module
public import NSP14.Homological.ActionSingleCoefficient
public import NSP14.Homological.RegularRestriction
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R σ : Type u) [Field k] [CommRing R] [Algebra k R]

noncomputable def regularPartialCoefficientComplex (rs : List R) : ChainComplex (ModuleCat.{u} k) ℕ :=
  nativeCoefficientComplex k R (actionRegularComplex R rs)

noncomputable def regularPartialPolynomialIso (φ : VariableRing k σ →ₐ[k] R) (xs : List σ) :
    regularPartialCoefficientComplex k R (xs.map (fun x => φ (MvPolynomial.X x))) ≅
      (coefficientKoszulListFunctor k σ xs).obj (polynomialRegularModule k σ R φ) :=
  polynomialActionCoefficientIso k R σ φ xs (ModuleCat.of R R)

noncomputable def regularExtendedCoefficientComplex (rs : List R)
    (φ : VariableRing k σ →ₐ[k] R) (xs : List σ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  nativeCoefficientComplex k R ((actionOnComplex R (xs.map (fun x => φ (MvPolynomial.X x)))).obj
    (actionRegularComplex R rs))
end NSP14.Homological
