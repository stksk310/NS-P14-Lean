module
public import NSP14.Homological.RegularActionCoefficient
public import NSP14.Homological.FullListBetti
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]

noncomputable def actionOnComplex_appendIso (xs ys : List R) (M : ModuleCat.{u} R) :
    (actionOnComplex R xs).obj ((actionKoszulFunctor R ys).obj M) ≅
      (actionKoszulFunctor R (xs++ys)).obj M := by
  induction xs with
  | nil => exact Iso.refl _
  | cons r rs ih => exact (scalarConeFunctor R r).mapIso ih

variable (k σ τ : Type u) [Field k] [Algebra k R]

/-- Regrouping actual elements into a complete formal variable list
identifies actual complexes; no spectral sequence is invoked. -/
noncomputable def regularExtendedPolynomialIso (rs : List R)
    (φ : VariableRing k σ →ₐ[k] R) (xs : List σ)
    (ψ : VariableRing k τ →ₐ[k] R) (ys : List τ)
    (h : ys.map (fun y => ψ (MvPolynomial.X y))=xs.map (fun x => φ (MvPolynomial.X x))++rs) :
    regularExtendedCoefficientComplex k R σ rs φ xs ≅
      (coefficientKoszulListFunctor k τ ys).obj (polynomialRegularModule k τ R ψ) :=
  (nativeCoefficientFunctor k R).mapIso (actionOnComplex_appendIso R _ rs (ModuleCat.of R R)) ≪≫
    eqToIso (congrArg (regularPartialCoefficientComplex k R) h.symm) ≪≫
      regularPartialPolynomialIso k R τ ψ ys

variable [Fintype τ]
theorem regularExtendedPolynomialBetti
    (rs : List R) (φ : VariableRing k σ →ₐ[k] R) (xs : List σ)
    (ψ : VariableRing k τ →ₐ[k] R) (ys : List τ)
    (h : ys.map (fun y => ψ (MvPolynomial.X y))=xs.map (fun x => φ (MvPolynomial.X x))++rs)
    (hall : ∀ y,y∈ys) (hnodup : ys.Nodup)
    [Module.Finite (VariableRing k τ) (polynomialRegularModule k τ R ψ)] (i : ℕ) :
    Module.finrank k ((regularExtendedCoefficientComplex k R σ rs φ xs).homology i)=
      totalBetti k τ (polynomialRegularModule k τ R ψ) i :=
  (coefficientComplexIso_finrank k (regularExtendedPolynomialIso R k σ τ rs φ xs ψ ys h) i).trans
    (fullList_totalBetti k τ ys hall hnodup (polynomialRegularModule k τ R ψ) i).symm
end NSP14.Homological
