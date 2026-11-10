module

public import NSP14.Homological.KoszulComplex

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u v w

variable (R : Type u) [CommRing R]

noncomputable def scalarConeFunctor (r : R) :
    ChainComplex (ModuleCat.{w} R) ℕ ⥤ ChainComplex (ModuleCat.{w} R) ℕ where
  obj K := HomologicalComplex.homotopyCofiber (r • 𝟙 K)
  map {K L} f := HomologicalComplex.homotopyCofiber.mapArrowHom (r • 𝟙 K) (r • 𝟙 L)
    (fun j => ⟨j+1,rfl⟩) (Arrow.homMk f f (by simp))
  map_id K := by
    change HomologicalComplex.homotopyCofiber.mapArrowHom (r • 𝟙 K) (r • 𝟙 K) _ _ = _
    have he : (Arrow.homMk (𝟙 K) (𝟙 K) (by simp) : Arrow.mk (r • 𝟙 K) ⟶ Arrow.mk (r • 𝟙 K))=𝟙 _ :=
      Arrow.hom_ext _ _ rfl rfl
    rw [he,HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  map_comp {K L N} f g := by
    change HomologicalComplex.homotopyCofiber.mapArrowHom (r • 𝟙 K) (r • 𝟙 N) _ _ = _
    rw [← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
    congr 1

variable (k : Type u) (σ : Type v) [CommRing k]

/-- A genuine functor of actual polynomial modules, preserving the variable list. -/
noncomputable def koszulFunctor (xs : List σ) :
    ModuleCat.{w} (VariableRing k σ) ⥤ ChainComplex (ModuleCat.{w} (VariableRing k σ)) ℕ :=
  match xs with
  | [] => ChainComplex.single₀ _
  | x::xs => koszulFunctor xs ⋙ scalarConeFunctor _ (MvPolynomial.X x)

theorem koszulFunctor_obj (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    (koszulFunctor k σ xs).obj M=koszulList k σ xs M := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change HomologicalComplex.homotopyCofiber (MvPolynomial.X x • 𝟙 ((koszulFunctor k σ xs).obj M)) = _
    rw [ih]
    rfl

/-- Homology is functorial for the same concrete variable differential. -/
noncomputable def koszulHomologyFunctor (xs : List σ) (i : ℕ) :
    ModuleCat.{w} (VariableRing k σ) ⥤ ModuleCat.{w} (VariableRing k σ) :=
  koszulFunctor k σ xs ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i

/-- Natural homology transport under any actual polynomial-module equivalence. -/
noncomputable def koszulHomologyIso (xs : List σ) (i : ℕ)
    {M N : ModuleCat.{w} (VariableRing k σ)} (e : M ≅ N) :
    (koszulHomologyFunctor k σ xs i).obj M ≅ (koszulHomologyFunctor k σ xs i).obj N :=
  (koszulHomologyFunctor k σ xs i).mapIso e

theorem koszul_homology_isZero_of_gt (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ))
    (i : ℕ) (hi : xs.length < i) : IsZero (koszulHomology k σ xs M i) :=
  HomologicalComplex.ExactAt.isZero_homology (HomologicalComplex.ExactAt.of_isZero
    (koszul_piece_isZero_of_gt k σ xs M i hi))

end NSP14.Homological
