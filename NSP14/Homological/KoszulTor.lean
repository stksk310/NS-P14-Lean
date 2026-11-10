module

public import NSP14.Homological.KoszulResolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]

/-- Any additive P-linear functor commutes with the actual recursive variable differential. -/
noncomputable def koszulMapFunctorIso
    (F : ModuleCat (VariableRing k σ) ⥤ ModuleCat (VariableRing k σ))
    [F.Additive] [F.Linear (VariableRing k σ)] (xs : List σ) (M : ModuleCat (VariableRing k σ)) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulList k σ xs M) ≅
      koszulList k σ xs (F.obj M) := by
  induction xs with
  | nil => exact (singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app M
  | cons x xs ih =>
    let K := koszulList k σ xs M
    let F' := F.mapHomologicalComplex (ComplexShape.down ℕ)
    have he : F'.map ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) =
        (MvPolynomial.X x : VariableRing k σ) • 𝟙 (F'.obj K) := by
      exact (F'.map_smul _ _).trans (congrArg (fun f => (MvPolynomial.X x : VariableRing k σ) • f) (F'.map_id K))
    exact homotopyCofiber.mapHomologicalComplexObjIso ((MvPolynomial.X x : VariableRing k σ) • 𝟙 K) F ≪≫
      eqToIso (by rw [he]; rfl) ≪≫
      (scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).mapIso ih

/-- Tensoring the polynomial-variable resolution with M gives its actual Koszul complex. -/
noncomputable def tensorKoszulIso (xs : List σ) (M : ModuleCat (VariableRing k σ)) :
    ((((tensoringLeft (ModuleCat (VariableRing k σ))).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ)))) ≅
        koszulList k σ xs M :=
  koszulMapFunctorIso k σ ((tensoringLeft _).obj M) xs _ ≪≫
    (by
      have hi := (koszulFunctor k σ xs).mapIso (ρ_ M)
      simp only [koszulFunctor_obj] at hi
      exact hi)

/-- Ordinary mathlib Tor derives the second tensor factor; here that factor is the residue field.
The proof uses the actual free resolution and tensor identification, not a renamed homology. -/
noncomputable def torKoszulIso [Fintype σ] (M : ModuleCat (VariableRing k σ)) (i : ℕ) :
    (((CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i).obj M).obj (residueField k σ)) ≅
      koszulHomology k σ (variableList k σ) M i :=
  (koszulResolution k σ).isoLeftDerivedObj ((tensoringLeft _).obj M) i ≪≫
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (tensorKoszulIso k σ _ M)

end NSP14.Homological
