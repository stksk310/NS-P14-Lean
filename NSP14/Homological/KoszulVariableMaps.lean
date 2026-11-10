module
public import NSP14.Homological.KoszulAnnihilation
public import NSP14.Homological.KoszulLinearity
public import NSP14.Homological.CoefficientKoszulFunctor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

theorem koszulHomology_map_variable (M : ModuleCat.{u} (VariableRing k σ)) (x : σ) (i : ℕ) :
    (koszulHomologyFunctor k σ (variableList k σ) i).map
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)=0 := by
  change homologyMap ((koszulFunctor k σ (variableList k σ)).map
    ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)) i=0
  rw [Functor.map_smul,(koszulFunctor k σ (variableList k σ)).map_id]
  rw [koszulFunctor_obj]
  simpa only [homologyMap_zero] using (koszulVariableHomotopy k σ M x).homologyMap_eq i

/-- Multiplication by a polynomial variable after any actual module map
induces the zero map on actual Koszul homology in every degree. -/
theorem koszulHomology_map_variable_multiple {M N : ModuleCat.{u} (VariableRing k σ)}
    (f : M ⟶ N) (x : σ) (i : ℕ) :
    (koszulHomologyFunctor k σ (variableList k σ) i).map
      (f ≫ ((MvPolynomial.X x : VariableRing k σ) • 𝟙 N))=0 := by
  rw [Functor.map_comp,koszulHomology_map_variable,comp_zero]

theorem coefficientKoszulHomology_map_variable (M : ModuleCat.{u} (VariableRing k σ)) (x : σ) (i : ℕ) :
    homologyMap ((coefficientKoszulFunctor k σ).map ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)) i=0 := by
  change homologyMap
    (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((koszulFunctor k σ (variableList k σ)).map ((MvPolynomial.X x : VariableRing k σ) • 𝟙 M))) i=0
  rw [Functor.map_smul,(koszulFunctor k σ (variableList k σ)).map_id,koszulFunctor_obj]
  have h := ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomotopy
    (koszulVariableHomotopy k σ M x)).homologyMap_eq i
  simpa only [Functor.map_zero,homologyMap_zero] using h

theorem coefficientKoszulHomology_map_variable_multiple {M N : ModuleCat.{u} (VariableRing k σ)}
    (f : M ⟶ N) (x : σ) (i : ℕ) :
    homologyMap ((coefficientKoszulFunctor k σ).map
      (f ≫ ((MvPolynomial.X x : VariableRing k σ) • 𝟙 N))) i=0 := by
  rw [Functor.map_comp,homologyMap_comp,coefficientKoszulHomology_map_variable,comp_zero]
end NSP14.Homological
