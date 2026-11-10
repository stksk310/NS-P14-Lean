module
public import NSP14.Homological.ActionOnComplex
public import NSP14.Homological.ActionCoefficient
public import NSP14.Homological.NativeCoefficientComplex
public import NSP14.Homological.ActionH0Image
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R σ : Type u) [Field k] [CommRing R] [Algebra k R]

noncomputable def coefficientComplexHomologyIso {K J : ChainComplex (ModuleCat.{u} k) ℕ}
    (e : K ≅ J) (i : ℕ) : K.homology i ≅ J.homology i :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso e

noncomputable def coefficientFullHomologyIso [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    ((coefficientKoszulFunctor k σ).obj M).homology i ≅ koszulHomologyK k σ M i :=
  coefficientKoszulHomologyIso k σ M i

noncomputable def coefficientCanonicalListHomologyIso [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    ((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).homology i ≅ koszulHomologyK k σ M i :=
  coefficientFullHomologyIso k σ M i

theorem coefficientComplexIso_finrank {K J : ChainComplex (ModuleCat.{u} k) ℕ}
    (e : K ≅ J) (i : ℕ) : Module.finrank k (K.homology i)=Module.finrank k (J.homology i) :=
  (coefficientComplexHomologyIso k e i).toLinearEquiv.finrank_eq

theorem coefficientCanonicalList_totalBetti [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.finrank k (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).homology i)=totalBetti k σ M i :=
  (coefficientCanonicalListHomologyIso k σ M i).toLinearEquiv.finrank_eq

noncomputable def actionSingleCoefficientIso (φ : VariableRing k σ →ₐ[k] R)
    (xs : List σ) (M : ModuleCat.{u} R) :
    nativeCoefficientComplex k R ((actionOnComplex R (xs.map (fun x => φ (MvPolynomial.X x)))).obj
      ((ChainComplex.single₀ _).obj M)) ≅
        (coefficientKoszulListFunctor k σ xs).obj ((ModuleCat.restrictScalars φ.toRingHom).obj M) :=
  (nativeCoefficientFunctor k R).mapIso (actionOnComplex_singleIso R _ M) ≪≫
    polynomialActionCoefficientIso k R σ φ xs M

noncomputable def actionH0SingleCoefficientComplex (rs : List R) (φ : VariableRing k σ →ₐ[k] R) (xs : List σ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  nativeCoefficientComplex k R ((actionOnComplex R (xs.map (fun x => φ (MvPolynomial.X x)))).obj
    ((ChainComplex.single₀ _).obj ((actionRegularComplex R rs).homology 0)))

/-- H0 here is the native homology of the original partial complex. -/
noncomputable def actionH0SingleCoefficientIso (rs : List R) (φ : VariableRing k σ →ₐ[k] R) (xs : List σ) :
    actionH0SingleCoefficientComplex k R σ rs φ xs ≅
        (coefficientKoszulListFunctor k σ xs).obj (actionRestrictedH0 rs φ.toRingHom) :=
  actionSingleCoefficientIso k R σ φ xs _
noncomputable def actionH0CanonicalCoefficientIso [Fintype σ] (rs : List R)
    (φ : VariableRing k σ →ₐ[k] R) :
    actionH0SingleCoefficientComplex k R σ rs φ (variableList k σ) ≅
      (coefficientKoszulFunctor k σ).obj (actionRestrictedH0 rs φ.toRingHom) :=
  actionH0SingleCoefficientIso k R σ rs φ (variableList k σ)

variable [Fintype σ] (rs : List R) (φ : VariableRing k σ →ₐ[k] R)
  [Module.Finite (VariableRing k σ) (actionRestrictedH0 rs φ.toRingHom)]

theorem actionH0Canonical_finite (i : ℕ) :
    Module.Finite k ((actionH0SingleCoefficientComplex k R σ rs φ (variableList k σ)).homology i) :=
  complex_homologyFinite_of_iso k (actionH0CanonicalCoefficientIso k R σ rs φ) i

theorem actionH0Canonical_betti (i : ℕ) :
    Module.finrank k ((actionH0SingleCoefficientComplex k R σ rs φ (variableList k σ)).homology i)=
      totalBetti k σ (actionRestrictedH0 rs φ.toRingHom) i :=
  (coefficientComplexIso_finrank k (actionH0SingleCoefficientIso k R σ rs φ (variableList k σ)) i).trans
    (coefficientCanonicalList_totalBetti k σ (actionRestrictedH0 rs φ.toRingHom) i)
end NSP14.Homological
