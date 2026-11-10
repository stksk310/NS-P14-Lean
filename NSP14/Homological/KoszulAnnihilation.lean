module

public import NSP14.Homological.KoszulTor
public import Mathlib.Algebra.Homology.ShortComplex.Linear

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

omit [Fintype σ] in
/-- Every variable acts by zero on the actual residue module. -/
theorem residueField_variable (x : σ) (a : residueField k σ) :
    (MvPolynomial.X x : VariableRing k σ) • a=0 := by
  change augmentation k σ (MvPolynomial.X x) * (show k from a)=0
  rw [augmentation_X, zero_mul]

/-- Projectivity and the proved exactness construct null-homotopies for every variable,
not only the last scalar cone. -/
noncomputable def polynomialVariableHomotopy (x : σ) :
    Homotopy ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulResolution k σ).complex) 0 :=
  ProjectiveResolution.liftHomotopyZero (P := koszulResolution k σ) (Q := koszulResolution k σ) _ (by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply ModuleCat.hom_ext
      ext a
      change ((koszulResolution k σ).π.f 0).hom ((MvPolynomial.X x : VariableRing k σ) • a)=0
      rw [map_smul]
      exact residueField_variable k σ x _
    | succ i => simp)

/-- Tensoring and the concrete complex identification transport all variable contractions. -/
noncomputable def koszulVariableHomotopy (M : ModuleCat.{u} (VariableRing k σ)) (x : σ) :
    Homotopy ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ (variableList k σ) M)) 0 := by
  let F := (CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{u} (VariableRing k σ))).obj M
  let e := tensorKoszulIso k σ (variableList k σ) M
  have h0 : Homotopy ((MvPolynomial.X x : VariableRing k σ) • 𝟙
      (koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ)))) 0 :=
    polynomialVariableHomotopy k σ x
  have h := ((F.mapHomotopy h0).compLeft e.inv).compRight e.hom
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq (by simp)))
  erw [Functor.map_smul, CategoryTheory.Functor.map_id]
  simp

/-- Scalar multiplication on homology is the homology map of the same chain scalar. -/
theorem complex_homologyMap_smul {R : Type u} [CommRing R]
    {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (r : R) (i : ℕ) :
    homologyMap (r • f) i = r • homologyMap f i := by
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ i).map (r • f)) = _
  have he : (shortComplexFunctor _ _ i).map (r • f) = r • (shortComplexFunctor _ _ i).map f := rfl
  rw [he, ShortComplex.homologyMap_smul]
  rfl

theorem koszul_homology_variable_annihilates (M : ModuleCat.{u} (VariableRing k σ))
    (i : ℕ) (x : σ) (a : koszulHomology k σ (variableList k σ) M i) :
    (MvPolynomial.X x : VariableRing k σ) • a=0 := by
  have he := (koszulVariableHomotopy k σ M x).homologyMap_eq i
  rw [complex_homologyMap_smul,homologyMap_id,homologyMap_zero] at he
  exact congrArg (fun f => f.hom a) he

/-- Homology with its coefficient-field action obtained by restriction, not a new vector-space model. -/
noncomputable def koszulHomologyK (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj
    (koszulHomology k σ (variableList k σ) M i)

noncomputable instance koszulHomologyKPolynomial (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    Module (VariableRing k σ) (koszulHomologyK k σ M i) :=
  inferInstanceAs (Module (VariableRing k σ) (koszulHomology k σ (variableList k σ) M i))

theorem koszul_homology_action_reduction (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ)
    (p : VariableRing k σ) (a : koszulHomologyK k σ M i) :
    p • a = augmentation k σ p • a := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    change (MvPolynomial.C c : VariableRing k σ) • a = augmentation k σ (MvPolynomial.C c) • a
    erw [(augmentation k σ).commutes c]
    rfl
  | add p q hp hq => rw [add_smul,hp,hq,map_add,add_smul]
  | mul_X p x hp =>
    have hz : (MvPolynomial.X x : VariableRing k σ) • a=0 :=
      koszul_homology_variable_annihilates k σ M i x a
    rw [mul_smul,hz,smul_zero,map_mul,augmentation_X,mul_zero,zero_smul]

/-- The chain groups may be infinite over k; finite P-homology and all-variable annihilation
supply the actual finite-dimensional homology. -/
theorem koszul_homology_finite (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) : Module.Finite k (koszulHomologyK k σ M i) := by
  let : Module.Finite (VariableRing k σ) (koszulHomologyK k σ M i) :=
    koszul_homology_polynomial_finite k σ _ M i
  exact finite_of_action_reduction (VariableRing k σ) k (koszulHomologyK k σ M i)
    (augmentation k σ) (fun p a => koszul_homology_action_reduction k σ M i p a)

end NSP14.Homological
