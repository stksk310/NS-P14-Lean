module

public import NSP14.Homological.HomologyBaseChangeNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory HomologicalComplex

namespace NSP14.Homological

universe u
variable {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)

@[reassoc (attr := simp)]
theorem normalizeCofiber_inr (a b : K ⟶ K) (h : a=b) (i : ℕ) :
    homotopyCofiber.inrX a i ≫ (eqToIso (congrArg (fun f => homotopyCofiber f) h)).hom.f i =
      homotopyCofiber.inrX b i := by subst b; simp

@[reassoc (attr := simp)]
theorem normalizeCofiber_inl (a b : K ⟶ K) (h : a=b) (i : ℕ) :
    homotopyCofiber.inlX a i (i+1) (natDownStep i) ≫
      (eqToIso (congrArg (fun f => homotopyCofiber f) h)).hom.f (i+1) =
    homotopyCofiber.inlX b i (i+1) (natDownStep i) := by subst b; simp

variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

@[reassoc (attr := simp)]
theorem polynomialConeComparison_inr (x : σ)
    (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) (i : ℕ) :
    (polynomialBaseChangeFunctor k L σ).map (homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) i) ≫
      (polynomialConeComparison k L σ x K).hom.f i =
    homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing L σ) •
      𝟙 (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj K)) i := by
  dsimp only [polynomialConeComparison,Iso.trans_hom,comp_f]
  rw [← Category.assoc]
  erw [homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom]
  exact normalizeCofiber_inr _ _ _ (polynomialBaseChangeCone_variable k L σ x K) i

@[reassoc (attr := simp)]
theorem polynomialConeComparison_inl (x : σ)
    (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) (i : ℕ) :
    (polynomialBaseChangeFunctor k L σ).map
        (homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) i (i+1) (natDownStep i)) ≫
      (polynomialConeComparison k L σ x K).hom.f (i+1) =
    homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing L σ) •
      𝟙 (((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj K)) i (i+1) (natDownStep i) := by
  dsimp only [polynomialConeComparison,Iso.trans_hom,comp_f]
  rw [← Category.assoc]
  erw [map_inl_cofiberComparison (polynomialBaseChangeFunctor k L σ)
    ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) i]
  exact normalizeCofiber_inl _ _ _ (polynomialBaseChangeCone_variable k L σ x K) i

variable {M : ModuleCat.{u} (VariableRing k σ)} {N : ModuleCat.{u} (VariableRing L σ)}

/-- The total comparison using exactly the actual coefficient-change module isomorphism e. -/
noncomputable def polynomialKoszulTotalIso
    (e : polynomialBaseChangeModule k L σ M ≅ N) (xs : List σ) :
    ((polynomialBaseChangeFunctor k L σ).mapHomologicalComplex _).obj (koszulList k σ xs M) ≅
      koszulList L σ xs N :=
  koszulPolynomialBaseChangeIso k L σ xs M ≪≫ (koszulFunctor L σ xs).mapIso e

@[reassoc (attr := simp)]
theorem polynomialKoszulTotalIso_inr
    (e : polynomialBaseChangeModule k L σ M ≅ N) (x : σ) (xs : List σ) (i : ℕ) :
    (polynomialBaseChangeFunctor k L σ).map
        (homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i) ≫
      (polynomialKoszulTotalIso k L σ e (x::xs)).hom.f i =
    (polynomialKoszulTotalIso k L σ e xs).hom.f i ≫
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing L σ) • 𝟙 (koszulList L σ xs N)) i := by
  simp only [polynomialKoszulTotalIso,Iso.trans_hom,comp_f,Functor.mapIso_hom,
    koszulPolynomialBaseChangeIso_cons]
  simp only [Category.assoc]
  erw [polynomialConeComparison_inr_assoc]
  erw [scalarCone_map_inr_assoc]
  change (koszulPolynomialBaseChangeIso k L σ xs M).hom.f i ≫
    homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing L σ) •
      𝟙 (koszulList L σ xs (polynomialBaseChangeModule k L σ M))) i ≫
      ((scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).map (koszulMap L σ xs e.hom)).f i = _
  rw [scalarCone_map_inr]
  rfl

@[reassoc (attr := simp)]
theorem polynomialKoszulTotalIso_inl
    (e : polynomialBaseChangeModule k L σ M ≅ N) (x : σ) (xs : List σ) (i : ℕ) :
    (polynomialBaseChangeFunctor k L σ).map
        (homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i (i+1) (natDownStep i)) ≫
      (polynomialKoszulTotalIso k L σ e (x::xs)).hom.f (i+1) =
    (polynomialKoszulTotalIso k L σ e xs).hom.f i ≫
      homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing L σ) • 𝟙 (koszulList L σ xs N)) i (i+1) (natDownStep i) := by
  simp only [polynomialKoszulTotalIso,Iso.trans_hom,comp_f,Functor.mapIso_hom,
    koszulPolynomialBaseChangeIso_cons]
  simp only [Category.assoc]
  erw [polynomialConeComparison_inl_assoc]
  erw [scalarCone_map_inl_assoc]
  change (koszulPolynomialBaseChangeIso k L σ xs M).hom.f i ≫
    homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing L σ) •
      𝟙 (koszulList L σ xs (polynomialBaseChangeModule k L σ M))) i (i+1) (natDownStep i) ≫
      ((scalarConeFunctor (VariableRing L σ) (MvPolynomial.X x)).map (koszulMap L σ xs e.hom)).f (i+1) = _
  rw [scalarCone_map_inl]
  rfl

end NSP14.Homological
