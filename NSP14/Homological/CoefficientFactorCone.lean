module
public import NSP14.Homological.CoefficientConeBetti
public import NSP14.Homological.FactorConeTerminal
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (xs : List σ)
  {K G I A : ModuleCat.{u} (VariableRing k σ)}
  (f : K ⟶ G) (g : G ⟶ I) (a : I ⟶ G) (b : G ⟶ A)
  (hfg : f ≫ g=0) (hab : a ≫ b=0)
  (h₁ : (ShortComplex.mk f g hfg).ShortExact) (h₂ : (ShortComplex.mk a b hab).ShortExact)
  [∀ i,Module.Finite k (((coefficientKoszulListFunctor k σ xs).obj K).homology i)]
  [∀ i,Module.Finite k (((coefficientKoszulListFunctor k σ xs).obj A).homology i)]

include f b hfg hab h₁ h₂ in
theorem coefficientFactorCone_Euler_comparison (j : ℕ) :
    complexEuler k (coefficientActionCone k σ xs G (g ≫ a)) (j+1) ≤
      complexEuler k ((coefficientKoszulListFunctor k σ xs).obj A) (j+1)+
        complexEuler k ((coefficientKoszulListFunctor k σ xs).obj K) j := by
  let F := coefficientKoszulListFunctor k σ xs
  have hF₁ := coefficientKoszulListFunctor_shortExact k σ xs (ShortComplex.mk f g hfg) h₁
  have hF₂ := coefficientKoszulListFunctor_shortExact k σ xs (ShortComplex.mk a b hab) h₂
  dsimp only [ShortComplex.map] at hF₁ hF₂
  have hfga : F.map f ≫ F.map g=0 := by rw [← F.map_comp,hfg,F.map_zero]
  have haba : F.map a ≫ F.map b=0 := by rw [← F.map_comp,hab,F.map_zero]
  have h := factorCone_Euler_comparison k (F.map f) (F.map g) (F.map a) (F.map b) hfga haba hF₁ hF₂ j
  rw [← F.map_comp] at h
  exact h

include f b hfg hab h₁ h₂ in
theorem coefficientFactorCone_Euler_zero (j : ℕ)
    (hK : complexEuler k ((coefficientKoszulListFunctor k σ xs).obj K) j=0)
    (hA : complexEuler k ((coefficientKoszulListFunctor k σ xs).obj A) (j+1)=0)
    (hz : IsZero (((coefficientKoszulListFunctor k σ xs).obj A).homology (j+2))) :
    complexEuler k (coefficientActionCone k σ xs G (g ≫ a)) (j+1)=0 := by
  let F := coefficientKoszulListFunctor k σ xs
  have hF₁ := coefficientKoszulListFunctor_shortExact k σ xs (ShortComplex.mk f g hfg) h₁
  have hF₂ := coefficientKoszulListFunctor_shortExact k σ xs (ShortComplex.mk a b hab) h₂
  dsimp only [ShortComplex.map] at hF₁ hF₂
  have hfga : F.map f ≫ F.map g=0 := by rw [← F.map_comp,hfg,F.map_zero]
  have haba : F.map a ≫ F.map b=0 := by rw [← F.map_comp,hab,F.map_zero]
  have h := factorCone_Euler_eq_zero_of_end k (F.map f) (F.map g) (F.map a) (F.map b)
    hfga haba hF₁ hF₂ j hK hA hz
  rw [← F.map_comp] at h
  exact h
end NSP14.Homological
