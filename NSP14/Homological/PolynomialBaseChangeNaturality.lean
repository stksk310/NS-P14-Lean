module

public import NSP14.Homological.KoszulPolynomialBaseChange

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

theorem polynomialBaseChangeCone_variable (x : σ)
    (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) =
    (MvPolynomial.X x : VariableRing L σ) • 𝟙
      (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact polynomialBaseChangeFunctor_variable k L σ (K.X i) x

noncomputable def polynomialConeComparison (x : σ)
    (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj
      ((scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).obj K) ≅
    (scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).obj
      (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj K) :=
  homotopyCofiber.mapHomologicalComplexObjIso ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K)
      (polynomialBaseChangeFunctor k L σ) ≪≫
    eqToIso (congrArg (fun f => homotopyCofiber f) (polynomialBaseChangeCone_variable k L σ x K))

@[reassoc]
theorem polynomialConeComparison_naturality (x : σ)
    {K J : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ} (f : K ⟶ J) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map
        ((scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).map f) ≫
      (polynomialConeComparison k L σ x J).hom =
    (polynomialConeComparison k L σ x K).hom ≫
      (scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).map
        (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map f) := by
  dsimp only [polynomialConeComparison,Iso.trans_hom]
  change ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map
    (homotopyCofiber.mapArrowHom ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K)
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 J) (fun j => ⟨j+1,natDownStep j⟩)
      (Arrow.homMk f f (by simp))) ≫ _ ≫ _ = _
  rw [cofiberMapComparison_naturality_assoc (F := polynomialBaseChangeFunctor k L σ)]
  erw [normalizeCofiber_naturality (MvPolynomial.X x) _ _
    (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map f) _
    (polynomialBaseChangeCone_variable k L σ x K) (polynomialBaseChangeCone_variable k L σ x J)]
  simp only [Category.assoc]

theorem koszulPolynomialBaseChangeIso_cons (x : σ) (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) :
    (koszulPolynomialBaseChangeIso k L σ (x::xs) M).hom =
      (polynomialConeComparison k L σ x (koszulList k σ xs M)).hom ≫
        (scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).map
          (koszulPolynomialBaseChangeIso k L σ xs M).hom := by
  simp only [koszulPolynomialBaseChangeIso,polynomialConeComparison,Iso.trans_hom,
    Functor.mapIso_hom,Category.assoc]

/-- Naturality of scalar extension for the original, actual signed Koszul maps. -/
@[reassoc]
theorem koszulPolynomialBaseChangeIso_naturality (xs : List σ)
    {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).map (koszulMap k σ xs f) ≫
      (koszulPolynomialBaseChangeIso k L σ xs N).hom =
    (koszulPolynomialBaseChangeIso k L σ xs M).hom ≫
      koszulMap L σ xs ((polynomialBaseChangeFunctor k L σ).map f) := by
  induction xs with
  | nil => exact (singleMapHomologicalComplex (polynomialBaseChangeFunctor k L σ) _ 0).hom.naturality f
  | cons x xs ih =>
    rw [koszulPolynomialBaseChangeIso_cons,koszulPolynomialBaseChangeIso_cons]
    change _ ≫ (polynomialConeComparison k L σ x (koszulList k σ xs N)).hom ≫ _ = _
    erw [polynomialConeComparison_naturality_assoc]
    rw [← CategoryTheory.Functor.map_comp,ih,CategoryTheory.Functor.map_comp]
    rfl

end NSP14.Homological
