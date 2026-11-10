module

public import NSP14.Homological.KoszulNaturality

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

namespace NSP14.Homological

universe u w
variable (R : Type u) [CommRing R]

noncomputable def scalarConeRaising (r : R) (K : ChainComplex (ModuleCat.{w} R) ℕ)
    (i j : ℕ) : (homotopyCofiber (r • 𝟙 K)).X i ⟶ (homotopyCofiber (r • 𝟙 K)).X j :=
  if h : (ComplexShape.down ℕ).Rel j i then
    homotopyCofiber.sndX (r • 𝟙 K) i ≫ homotopyCofiber.inlX (r • 𝟙 K) i j h else 0

/-- Multiplication by the newly adjoined variable is explicitly null-homotopic. -/
noncomputable def scalarConeHomotopy (r : R) (K : ChainComplex (ModuleCat.{w} R) ℕ) :
    Homotopy (r • 𝟙 (homotopyCofiber (r • 𝟙 K))) 0 where
  hom := scalarConeRaising R r K
  zero i j h := dite_eq_right h
  comm i := by
    let φ := r • 𝟙 K
    have hn : ¬(ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
      intro h; change (ComplexShape.down ℕ).next 0+1=0 at h; omega
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 hn,prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      simp only [zero_add]
      apply homotopyCofiber.ext_to_X' φ 0 hn
      simp [scalarConeRaising,φ,Category.assoc,homotopyCofiber.inlX_d']
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i+2) (i+1) from rfl)]
      apply homotopyCofiber.ext_to_X φ (i+1) i rfl
      · simp [scalarConeRaising,φ,Category.assoc,Preadditive.add_comp,
          homotopyCofiber.d_sndX]
        rw [homotopyCofiber.d_fstX _ (i+2) (i+1) i rfl rfl]
        simp
      · simp [scalarConeRaising,φ,Category.assoc,Preadditive.add_comp,
          homotopyCofiber.d_sndX]

end NSP14.Homological
