module
public import NSP14.Homological.CoefficientKoszulListFunctor
public import NSP14.Homological.KoszulLinearity
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]

/-- Adding a variable is the actual cone of its action on the preceding
Koszul complex, including restriction to the coefficient field. -/
noncomputable def coefficientKoszulListConsIso (x : σ) (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) :
    (coefficientKoszulListFunctor k σ (x::xs)).obj M ≅
      homotopyCofiber ((coefficientKoszulListFunctor k σ xs).map
        ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)) := by
  let F := (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex (ComplexShape.down ℕ)
  have he : (coefficientKoszulListFunctor k σ xs).map
        ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)=
      F.map ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) := by
    change F.map (koszulMap k σ xs ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M))=_
    rw [koszulMap_scalar]
  change F.obj (homotopyCofiber ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M))) ≅ _
  exact homotopyCofiber.mapHomologicalComplexObjIso _
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))) ≪≫
      eqToIso (congrArg (fun f : F.obj (koszulList k σ xs M) ⟶ F.obj (koszulList k σ xs M) =>
        homotopyCofiber f) he.symm)

noncomputable def coefficientFunctorConsIso {B : Type u} [Ring B]
    (F : ModuleCat.{u} B ⥤ ModuleCat.{u} (VariableRing k σ))
    (x : σ) (xs : List σ) (M : ModuleCat.{u} B) (f : M ⟶ M)
    (h : F.map f=(MvPolynomial.X x : VariableRing k σ) • 𝟙 (F.obj M)) :
    (coefficientKoszulListFunctor k σ (x::xs)).obj (F.obj M) ≅
      homotopyCofiber ((F ⋙ coefficientKoszulListFunctor k σ xs).map f) := by
  let H := coefficientKoszulListFunctor k σ xs
  let Φ : (F.obj M ⟶ F.obj M) → ChainComplex (ModuleCat.{u} k) ℕ :=
    fun q => homotopyCofiber (H.map q)
  exact coefficientKoszulListConsIso k σ x xs (F.obj M) ≪≫
    eqToIso (congrArg Φ h.symm) ≪≫ eqToIso rfl
end NSP14.Homological
