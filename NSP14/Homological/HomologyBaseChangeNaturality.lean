module

public import NSP14.Homological.PolynomialBaseChangeNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable {R T : Type u} [CommRing R] [CommRing T]

/-- Flat/exact homology comparison is a natural isomorphism, also for infinite chains. -/
noncomputable def homologyBaseChangeNatIso (F : ModuleCat.{u} R ⥤ ModuleCat.{u} T)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (i : ℕ) :
    F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ homologyFunctor _ (ComplexShape.down ℕ) i ≅
      homologyFunctor _ (ComplexShape.down ℕ) i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso F) (fun f =>
    ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor _ (ComplexShape.down ℕ) i).map f) F)

variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

/-- Scalar extension commutes naturally with the actual signed Koszul functor. -/
noncomputable def polynomialKoszulBaseChangeNatIso (xs : List σ) :
    koszulFunctor k σ xs ⋙ (polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _ ≅
      polynomialBaseChangeFunctor k L σ ⋙ koszulFunctor L σ xs :=
  NatIso.ofComponents (koszulPolynomialBaseChangeIso k L σ xs)
    (koszulPolynomialBaseChangeIso_naturality k L σ xs)

/-- The induced natural isomorphism on homology over the changed polynomial ring. -/
noncomputable def polynomialKoszulHomologyBaseChangeNatIso (xs : List σ) (i : ℕ) :
    (koszulFunctor k σ xs ⋙ (polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _) ⋙
      homologyFunctor _ (ComplexShape.down ℕ) i ≅
    (polynomialBaseChangeFunctor k L σ ⋙ koszulFunctor L σ xs) ⋙
      homologyFunctor _ (ComplexShape.down ℕ) i :=
  CategoryTheory.Functor.isoWhiskerRight (polynomialKoszulBaseChangeNatIso k L σ xs) _

end NSP14.Homological
