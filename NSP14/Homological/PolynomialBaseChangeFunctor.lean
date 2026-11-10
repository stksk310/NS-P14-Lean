module

public import NSP14.Homological.PolynomialBaseChangeModule

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]

noncomputable def coefficientMap {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) :
    coefficientModule k σ M →ₗ[k] coefficientModule k σ N :=
  ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map f).hom

theorem polynomialBaseChangeMap_variable {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N)
    (x : σ) (a : L ⊗[k] coefficientModule k σ M) :
    (coefficientMap k σ f).baseChange L (extendedPolynomialRepresentation k L σ M (MvPolynomial.X x) a) =
      extendedPolynomialRepresentation k L σ N (MvPolynomial.X x) ((coefficientMap k σ f).baseChange L a) := by
  induction a using TensorProduct.inductionOn with
  | tmul c m =>
    rw [polynomialBaseChange_variable,LinearMap.baseChange_tmul,LinearMap.baseChange_tmul,
      polynomialBaseChange_variable]
    have he : coefficientMap k σ f ((MvPolynomial.X x : VariableRing k σ) • m) =
        (MvPolynomial.X x : VariableRing k σ) • coefficientMap k σ f m := f.hom.map_smul _ _
    exact congrArg (fun n : coefficientModule k σ N => c ⊗ₜ[k] n) he

  | add a b ha hb => simp only [map_add,ha,hb]

theorem polynomialBaseChangeMap_linear {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N)
    (p : VariableRing L σ) (a : L ⊗[k] coefficientModule k σ M) :
    (coefficientMap k σ f).baseChange L (extendedPolynomialRepresentation k L σ M p a) =
      extendedPolynomialRepresentation k L σ N p ((coefficientMap k σ f).baseChange L a) := by
  induction p using MvPolynomial.induction_on generalizing a with
  | C c =>
    change (coefficientMap k σ f).baseChange L
      (extendedPolynomialRepresentation k L σ M (algebraMap L (VariableRing L σ) c) a) =
      extendedPolynomialRepresentation k L σ N (algebraMap L (VariableRing L σ) c)
        ((coefficientMap k σ f).baseChange L a)
    rw [(extendedPolynomialRepresentation k L σ M).commutes,
      (extendedPolynomialRepresentation k L σ N).commutes]
    exact map_smul ((coefficientMap k σ f).baseChange L) c a
  | add p q hp hq =>
    rw [map_add,map_add]
    change (coefficientMap k σ f).baseChange L (_+_) = _+_
    rw [map_add,hp,hq]
  | mul_X p x hp =>
    rw [map_mul,map_mul]
    change (coefficientMap k σ f).baseChange L
      (extendedPolynomialRepresentation k L σ M p (extendedPolynomialRepresentation k L σ M (MvPolynomial.X x) a)) = _
    rw [hp,polynomialBaseChangeMap_variable]
    rfl

noncomputable def polynomialBaseChangeMap {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) :
    polynomialBaseChangeModule k L σ M ⟶ polynomialBaseChangeModule k L σ N :=
  ModuleCat.ofHom (X := polynomialBaseChangeModule k L σ M) (Y := polynomialBaseChangeModule k L σ N)
    { toFun := (coefficientMap k σ f).baseChange L
      map_add' := map_add _
      map_smul' := polynomialBaseChangeMap_linear k L σ f }

noncomputable def polynomialBaseChangeFunctor :
    ModuleCat.{u} (VariableRing k σ) ⥤ ModuleCat.{u} (VariableRing L σ) where
  obj := polynomialBaseChangeModule k L σ
  map := polynomialBaseChangeMap k L σ
  map_id M := by
    apply ModuleCat.hom_ext
    ext a
    change ((coefficientMap k σ (𝟙 M)).baseChange L) a = a
    change (LinearMap.id.baseChange L) a = a
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext a
    change ((coefficientMap k σ (f ≫ g)).baseChange L) a =
      ((coefficientMap k σ g).baseChange L) (((coefficientMap k σ f).baseChange L) a)
    exact congrArg (fun h => h a) (LinearMap.baseChange_comp (coefficientMap k σ f) (coefficientMap k σ g))

noncomputable instance polynomialBaseChangeFunctor_additive : (polynomialBaseChangeFunctor k L σ).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    ext a
    change ((coefficientMap k σ (f+g)).baseChange L) a =
      ((coefficientMap k σ f).baseChange L) a + ((coefficientMap k σ g).baseChange L) a
    exact congrArg (fun h => h a) (LinearMap.baseChange_add (coefficientMap k σ f) (coefficientMap k σ g))

/-- Actual variable multiplication is preserved, with the changed coefficient ring. -/
theorem polynomialBaseChangeFunctor_variable (M : ModuleCat.{u} (VariableRing k σ)) (x : σ) :
    (polynomialBaseChangeFunctor k L σ).map
      (ModuleCat.ofHom (X := M) (Y := M) (variableOperator k σ M x)) =
        ModuleCat.ofHom (X := (polynomialBaseChangeFunctor k L σ).obj M) (Y := (polynomialBaseChangeFunctor k L σ).obj M)
          (variableOperator L σ ((polynomialBaseChangeFunctor k L σ).obj M) x) := by
  apply ModuleCat.hom_ext
  ext a
  change ((coefficientMap k σ (ModuleCat.ofHom (X := M) (Y := M) (variableOperator k σ M x))).baseChange L) a =
    extendedPolynomialRepresentation k L σ M (MvPolynomial.X x) a
  induction a using TensorProduct.inductionOn with
  | tmul c m =>
    rw [LinearMap.baseChange_tmul,polynomialBaseChange_variable]
    rfl
  | add a b ha hb => simp only [map_add,ha,hb]

end NSP14.Homological
