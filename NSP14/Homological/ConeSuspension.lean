module
public import NSP14.Homological.ConeDiagram
public import NSP14.Homological.ZeroCone
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R]
  (K : ChainComplex (ModuleCat.{w} R) ℕ)

noncomputable def zeroIdSequence : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ) :=
  ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat.{w} R) ℕ) ⟶ K) (𝟙 K) (by simp)

noncomputable def idZeroSequence : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ) :=
  ShortComplex.mk (𝟙 K) (0 : K ⟶ (0 : ChainComplex (ModuleCat.{w} R) ℕ)) (by simp)

theorem zeroIdSequence_shortExact : (zeroIdSequence R K).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine ⟨0,𝟙 K,?_,?_,?_⟩
  · exact (CategoryTheory.Limits.isZero_zero _).eq_of_src _ _
  · simp [zeroIdSequence]
  · simp [zeroIdSequence]

theorem idZeroSequence_shortExact : (idZeroSequence R K).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine ⟨𝟙 K,0,?_,?_,?_⟩
  · simp [idZeroSequence]
  · exact (CategoryTheory.Limits.isZero_zero _).eq_of_src _ _
  · simp [idZeroSequence]

noncomputable def coneSuspension : ChainComplex (ModuleCat.{w} R) ℕ :=
  homotopyCofiber (0 : K ⟶ (0 : ChainComplex (ModuleCat.{w} R) ℕ))

noncomputable def coneSuspensionDiagram : zeroIdSequence R K ⟶ idZeroSequence R K :=
  ShortComplex.homMk 0 (𝟙 K) 0 (by simp [zeroIdSequence,idZeroSequence]) (by simp [zeroIdSequence,idZeroSequence])

noncomputable def coneSuspensionHomologyIso (i : ℕ) :
    (coneSuspension R K).homology (i+1) ≅ K.homology i := by
  let h := coneDiagram_shortExact R (coneSuspensionDiagram R K)
    (zeroIdSequence_shortExact R K) (idZeroSequence_shortExact R K)
  exact h.δIso (i+1) i (natDownStep i)
    (identityCone_homology_isZero R K (i+1)) (identityCone_homology_isZero R K i) ≪≫
      (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso R K)

theorem coneSuspension_homology_zero : IsZero ((coneSuspension R K).homology 0) := by
  have hz : IsZero ((coneSuspension R K).X 0) := by
    have h0 : IsZero ((0 : ChainComplex (ModuleCat.{w} R) ℕ).X 0) :=
      (eval (ModuleCat.{w} R) (ComplexShape.down ℕ) 0).map_isZero (CategoryTheory.Limits.isZero_zero _)
    exact IsZero.of_iso h0 (arrowConeZeroIso R (0 : K ⟶ (0 : ChainComplex (ModuleCat.{w} R) ℕ)))
  exact ((coneSuspension R K).sc 0).exact_iff_isZero_homology.mp
    (((coneSuspension R K).sc 0).exact_of_isZero_X₂ hz)
end NSP14.Homological
