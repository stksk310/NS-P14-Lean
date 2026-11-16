module
public import NSP14.Homological.ComplexEuler
public import NSP14.Homological.BettiEuler
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable def coefficientKoszulFunctor :
    ModuleCat.{u} (VariableRing k σ) ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  koszulFunctor k σ (variableList k σ) ⋙
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex (ComplexShape.down ℕ)

noncomputable instance coefficientKoszulFunctor_additive : (coefficientKoszulFunctor k σ).Additive := by
  unfold coefficientKoszulFunctor
  infer_instance

theorem coefficientKoszulFunctor_obj (M : ModuleCat.{u} (VariableRing k σ)) :
    (coefficientKoszulFunctor k σ).obj M=coefficientKoszulComplex k σ M := rfl

noncomputable instance coefficientKoszulFunctor_homologyFinite
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.Finite k (((coefficientKoszulFunctor k σ).obj M).homology i) := by
  rw [coefficientKoszulFunctor_obj]
  infer_instance

theorem coefficientKoszulFunctor_shortExact (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) : (S.map (coefficientKoszulFunctor k σ)).ShortExact :=
  coefficientKoszulSequence_shortExact k σ S hS

theorem complexEuler_coefficientKoszul (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (j : ℕ) :
    complexEuler k ((coefficientKoszulFunctor k σ).obj M) j=bettiEuler k σ M j := by
  unfold complexEuler bettiEuler
  congr 1
  funext i
  exact (coefficientKoszulHomologyIso k σ M i).toLinearEquiv.finrank_eq
end NSP14.Homological
