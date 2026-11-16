module
public import NSP14.Homological.ArrowCone
public import NSP14.Homological.KoszulAnnihilation
public import NSP14.Homological.KoszulContraction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{w} R) ℕ)

noncomputable def zeroArrowConeIso :
    homotopyCofiber (0 : (0 : ChainComplex (ModuleCat.{w} R) ℕ) ⟶ K) ≅ K where
  hom := homotopyCofiber.desc _ (𝟙 K) (Homotopy.ofEq (by simp))
  inv := homotopyCofiber.inr _
  inv_hom_id := homotopyCofiber.inr_desc _ _ _
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply homotopyCofiber.ext_from_X' (0 : (0 : ChainComplex (ModuleCat.{w} R) ℕ) ⟶ K) 0 (by intro h;change _+1=0 at h;omega)
      simp
    | succ i =>
      apply homotopyCofiber.ext_from_X (0 : (0 : ChainComplex (ModuleCat.{w} R) ℕ) ⟶ K) i (i+1) (natDownStep i)
      · have hz : IsZero ((0 : ChainComplex (ModuleCat.{w} R) ℕ).X i) :=
          (eval (ModuleCat.{w} R) (ComplexShape.down ℕ) i).map_isZero
            (CategoryTheory.Limits.isZero_zero _)
        exact hz.eq_of_src _ _
      · simp

/-- The identity cone is contractible by the existing actual raising
homotopy, including when its chain groups are infinite dimensional. -/
theorem identityCone_homology_isZero (i : ℕ) :
    IsZero ((homotopyCofiber (𝟙 K)).homology i) := by
  have h := scalarConeHomotopy R 1 K
  simp only [one_smul] at h
  have he := h.homologyMap_eq i
  simp only [homologyMap_id,homologyMap_zero] at he
  simpa only [one_smul] using (IsZero.iff_id_eq_zero _).mpr he
end NSP14.Homological
