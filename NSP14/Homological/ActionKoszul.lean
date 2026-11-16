module
public import NSP14.Homological.PolynomialRestrictionKoszul
public import NSP14.Homological.ConeDiagram
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]

/-- Koszul on actual ring elements, retaining their native module action. -/
noncomputable def actionKoszulFunctor : List R →
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ
  | [] => ChainComplex.single₀ _
  | r::rs => actionKoszulFunctor rs ⋙ scalarConeFunctor R r

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

theorem restrict_action_chain (r : R) (K : ChainComplex (ModuleCat.{u} S) ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (φ r • 𝟙 K)=r • 𝟙 (((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  ext a
  rfl

/-- Native scalar actions commute with restriction, including on infinite modules. -/
noncomputable def actionKoszulRestrictionIso (rs : List R) (M : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((actionKoszulFunctor S (rs.map φ)).obj M) ≅
        (actionKoszulFunctor R rs).obj ((ModuleCat.restrictScalars φ).obj M) := by
  induction rs with
  | nil => exact (singleMapHomologicalComplex (ModuleCat.restrictScalars φ) (ComplexShape.down ℕ) 0).app M
  | cons r rs ih =>
    let K := (actionKoszulFunctor S (rs.map φ)).obj M
    exact homotopyCofiber.mapHomologicalComplexObjIso
        (φ r • 𝟙 K) (ModuleCat.restrictScalars φ) ≪≫
      eqToIso (by rw [restrict_action_chain φ r K];rfl) ≪≫
      (scalarConeFunctor R r).mapIso ih

variable (k σ : Type u) [CommRing k]
/-- The ordinary variable complex is the same native-action construction. -/
noncomputable def variableActionKoszulIso (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ)) :
    (actionKoszulFunctor (VariableRing k σ) (xs.map MvPolynomial.X)).obj M ≅
      koszulList k σ xs M := by
  induction xs with
  | nil => exact Iso.refl _
  | cons x xs ih => exact (scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).mapIso ih

/-- Native algebra action computes the polynomial-variable Koszul complex
without forgetting any commuting native scalars. -/
noncomputable def polynomialActionKoszulIso {A : Type u} [CommRing A]
    (φ : VariableRing k σ →+* A) (xs : List σ) (M : ModuleCat.{u} A) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((actionKoszulFunctor A (xs.map (fun x => φ (MvPolynomial.X x)))).obj M) ≅
        koszulList k σ xs ((ModuleCat.restrictScalars φ).obj M) := by
  simpa only [List.map_map,Function.comp_def] using
    actionKoszulRestrictionIso φ (xs.map MvPolynomial.X) M ≪≫
      variableActionKoszulIso k σ xs _
end NSP14.Homological
