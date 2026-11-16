module
public import NSP14.Homological.TwoStepCone
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k]
  {K G I A : ChainComplex (ModuleCat.{u} k) ℕ}
  (f : K ⟶ G) (g : G ⟶ I) (a : I ⟶ G) (b : G ⟶ A)
  (hfg : f ≫ g=0) (hab : a ≫ b=0)
  (h₁ : (ShortComplex.mk f g hfg).ShortExact) (h₂ : (ShortComplex.mk a b hab).ShortExact)
  [∀ i,Module.Finite k (K.homology i)] [∀ i,Module.Finite k (A.homology i)]

include f hfg h₁ b hab h₂ in
theorem factorCone_Euler_eq_zero_of_end (j : ℕ)
    (hK : complexEuler k K j=0) (hA : complexEuler k A (j+1)=0)
    (hz : IsZero (A.homology (j+2))) :
    complexEuler k (homotopyCofiber (g ≫ a)) (j+1)=0 := by
  rw [factorCone_Euler_eq k f g a b hfg hab h₁ h₂ j,hK,hA,
    factorConeCorrection_zero_of_quotient_homology_isZero k g a b hab h₂ (j+1)
      (by simpa only [Nat.add_assoc] using hz)]
  simp
end NSP14.Homological
