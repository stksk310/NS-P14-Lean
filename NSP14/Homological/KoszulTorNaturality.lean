module

public import NSP14.Homological.CofiberNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace NSP14.Homological

universe u
variable {R : Type u} [CommRing R]

noncomputable def mapScalarConeIso
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [F.Linear R]
    (r : R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (F.mapHomologicalComplex _).obj (homotopyCofiber (r • 𝟙 K)) ≅
      (scalarConeFunctor R r).obj ((F.mapHomologicalComplex _).obj K) :=
  homotopyCofiber.mapHomologicalComplexObjIso (r • 𝟙 K) F ≪≫
    eqToIso (by erw [Functor.map_smul,CategoryTheory.Functor.map_id]; rfl)

theorem normalizeCofiber_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (r : R) (a : K ⟶ K) (b : L ⟶ L)
    (f : K ⟶ L) (w : f ≫ b=a ≫ f) (ha : a=r • 𝟙 K) (hb : b=r • 𝟙 L) :
    homotopyCofiber.mapArrowHom a b (fun j => ⟨j+1,natDownStep j⟩) (Arrow.homMk f f w) ≫
      (eqToIso (congrArg (fun t : L ⟶ L => homotopyCofiber t) hb)).hom =
    (eqToIso (congrArg (fun t : K ⟶ K => homotopyCofiber t) ha)).hom ≫
      (scalarConeFunctor R r).map f := by
  subst a b
  simp only [eqToIso_refl,Iso.refl_hom,Category.comp_id,Category.id_comp]
  rfl

@[reassoc]
theorem mapScalarConeIso_naturality
    (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [G.Additive]
    [F.Linear R] [G.Linear R] (τ : F ⟶ G) (r : R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (τ.mapHomologicalComplex _).app (homotopyCofiber (r • 𝟙 K)) ≫
      (mapScalarConeIso G r K).hom =
    (mapScalarConeIso F r K).hom ≫
      (scalarConeFunctor R r).map ((τ.mapHomologicalComplex _).app K) := by
  dsimp only [mapScalarConeIso,Iso.trans_hom]
  rw [cofiberComparison_naturality_assoc F G τ]
  rw [normalizeCofiber_naturality r _ _ _ _
    (by erw [Functor.map_smul,CategoryTheory.Functor.map_id])
    (by erw [Functor.map_smul,CategoryTheory.Functor.map_id])]
  simp only [Category.assoc]

variable (k σ : Type u) [Field k]

theorem koszulMapFunctorIso_cons
    (F : ModuleCat.{u} (VariableRing k σ) ⥤ ModuleCat.{u} (VariableRing k σ))
    [F.Additive] [F.Linear (VariableRing k σ)] (x : σ) (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) :
    (koszulMapFunctorIso k σ F (x::xs) M).hom =
      (mapScalarConeIso F (MvPolynomial.X x) (koszulList k σ xs M)).hom ≫
        (scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).map
          (koszulMapFunctorIso k σ F xs M).hom := by
  simp only [koszulMapFunctorIso,mapScalarConeIso,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]

/-- The functor comparison is compatible with actual natural transformations. -/
@[reassoc]
theorem koszulMapFunctorIso_naturality
    (F G : ModuleCat.{u} (VariableRing k σ) ⥤ ModuleCat.{u} (VariableRing k σ))
    [F.Additive] [G.Additive] [F.Linear (VariableRing k σ)] [G.Linear (VariableRing k σ)]
    (τ : F ⟶ G) (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ)) :
    (τ.mapHomologicalComplex _).app (koszulList k σ xs M) ≫ (koszulMapFunctorIso k σ G xs M).hom =
    (koszulMapFunctorIso k σ F xs M).hom ≫ (koszulFunctor k σ xs).map (τ.app M) := by
  induction xs with
  | nil =>
    change (τ.mapHomologicalComplex _).app ((single _ _ 0).obj M) ≫
      ((singleMapHomologicalComplex G _ 0).app M).hom = _
    rw [natTransMapHomologicalComplex_app_single_obj]
    simp
    rfl
  | cons x xs ih =>
    rw [koszulMapFunctorIso_cons,koszulMapFunctorIso_cons,Category.assoc]
    change (τ.mapHomologicalComplex _).app (homotopyCofiber ((MvPolynomial.X x : VariableRing k σ) •
      𝟙 (koszulList k σ xs M))) ≫ _ = _
    rw [mapScalarConeIso_naturality_assoc F G τ]
    rw [← CategoryTheory.Functor.map_comp,ih,CategoryTheory.Functor.map_comp]
    rfl

@[reassoc]
theorem tensorKoszulIso_naturality (xs : List σ)
    {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) :
    (NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app
      (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))) ≫
        (tensorKoszulIso k σ xs N).hom =
      (tensorKoszulIso k σ xs M).hom ≫ (koszulFunctor k σ xs).map f := by
  dsimp only [tensorKoszulIso,Iso.trans_hom]
  rw [koszulMapFunctorIso_naturality_assoc k σ]
  calc
    _ = (koszulMapFunctorIso k σ ((tensoringLeft _).obj M) xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom ≫
      (koszulFunctor k σ xs).map (((tensoringLeft _).map f).app (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) ≫ (ρ_ N).hom) := by
        simp only [Functor.mapIso_hom,Functor.map_comp]
    _ = (koszulMapFunctorIso k σ ((tensoringLeft _).obj M) xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom ≫
      (koszulFunctor k σ xs).map ((ρ_ M).hom ≫ f) := by
        have he : ((tensoringLeft _).map f).app (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) ≫
            (ρ_ N).hom = (ρ_ M).hom ≫ f := rightUnitor_naturality f
        rw [he]
    _ = _ := by simp only [Functor.map_comp,Functor.mapIso_hom,Category.assoc]

/-- Naturality of ordinary Tor comparison in the actual module map. -/
@[reassoc]
theorem torKoszulIso_naturality [Fintype σ]
    {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) (i : ℕ) :
    ((CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i).map f).app (residueField k σ) ≫
      (torKoszulIso k σ N i).hom =
    (torKoszulIso k σ M i).hom ≫ (koszulHomologyFunctor k σ (variableList k σ) i).map f := by
  change (NatTrans.leftDerived ((tensoringLeft _).map f) i).app _ ≫ _ = _
  rw [ProjectiveResolution.leftDerived_app_eq _ (koszulResolution k σ)]
  dsimp only [torKoszulIso,Iso.trans_hom,koszulHomologyFunctor,Functor.comp_map]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Functor.mapIso_hom]
  have he := (homologyFunctor (ModuleCat (VariableRing k σ)) (ComplexShape.down ℕ) i).congr_map
    (tensorKoszulIso_naturality k σ (variableList k σ) f)
  rw [CategoryTheory.Functor.map_comp,CategoryTheory.Functor.map_comp] at he
  exact congrArg (fun v => ((koszulResolution k σ).isoLeftDerivedObj ((tensoringLeft _).obj M) i).hom ≫ v) he

end NSP14.Homological
