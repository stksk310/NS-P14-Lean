module

public import NSP14.Homological.KoszulExactness
public import NSP14.Homological.KoszulTor

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable {R : Type u} [CommRing R]
variable {K L K' L' : ChainComplex (ModuleCat.{u} R) ℕ}

@[reassoc (attr := simp)]
theorem cofiberMap_inl (φ : K ⟶ L) (ψ : K' ⟶ L') (a : Arrow.mk φ ⟶ Arrow.mk ψ) (i : ℕ) :
    homotopyCofiber.inlX φ i (i+1) (natDownStep i) ≫
      (homotopyCofiber.mapArrowHom φ ψ (fun j => ⟨j+1,natDownStep j⟩) a).f (i+1) =
        a.left.f i ≫ homotopyCofiber.inlX ψ i (i+1) (natDownStep i) := by
  change homotopyCofiber.inlX _ i (i+1) (natDownStep i) ≫ (homotopyCofiber.desc _ _ _).f (i+1) = _
  erw [homotopyCofiber.inlX_desc_f _ _ _ i (i+1) (natDownStep i)]
  simp [homotopyCofiber.inrCompHomotopy_hom]

@[reassoc (attr := simp)]
theorem cofiberMap_inr (φ : K ⟶ L) (ψ : K' ⟶ L') (a : Arrow.mk φ ⟶ Arrow.mk ψ) (i : ℕ) :
    homotopyCofiber.inrX φ i ≫
      (homotopyCofiber.mapArrowHom φ ψ (fun j => ⟨j+1,natDownStep j⟩) a).f i =
        a.right.f i ≫ homotopyCofiber.inrX ψ i := by
  simp [homotopyCofiber.mapArrowHom]

variable {R' : Type u} [CommRing R']
variable (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R') [F.Additive] [G.Additive]

@[reassoc (attr := simp)]
theorem map_inl_cofiberComparison (φ : K ⟶ L) (i : ℕ) :
    F.map (homotopyCofiber.inlX φ i (i+1) (natDownStep i)) ≫
      (homotopyCofiber.mapHomologicalComplexObjIso φ F).hom.f (i+1) =
        homotopyCofiber.inlX ((F.mapHomologicalComplex _).map φ) i (i+1) (natDownStep i) := by
  change F.map (homotopyCofiber.inlX φ i (i+1) (natDownStep i)) ≫
    (homotopyCofiber.mapHomologicalComplexObjXIso φ F (i+1)).hom = _
  rw [← cancel_mono (homotopyCofiber.mapHomologicalComplexObjXIso φ F (i+1)).inv,
    Category.assoc,Iso.hom_inv_id,Category.comp_id]
  exact (homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv φ F i (i+1) (natDownStep i)).symm

/-- Cofiber comparison is natural in actual commutative squares of chain maps,
including functors which change the coefficient ring. -/
@[reassoc]
theorem cofiberMapComparison_naturality (φ : K ⟶ L) (ψ : K' ⟶ L')
    (a : Arrow.mk φ ⟶ Arrow.mk ψ) :
    (F.mapHomologicalComplex _).map
        (homotopyCofiber.mapArrowHom φ ψ (fun j => ⟨j+1,natDownStep j⟩) a) ≫
      (homotopyCofiber.mapHomologicalComplexObjIso ψ F).hom =
    (homotopyCofiber.mapHomologicalComplexObjIso φ F).hom ≫
      homotopyCofiber.mapArrowHom ((F.mapHomologicalComplex _).map φ)
        ((F.mapHomologicalComplex _).map ψ) (fun j => ⟨j+1,natDownStep j⟩)
        (Arrow.homMk ((F.mapHomologicalComplex _).map a.left) ((F.mapHomologicalComplex _).map a.right)
          (by
            change (F.mapHomologicalComplex _).map a.left ≫ (F.mapHomologicalComplex _).map ψ =
              (F.mapHomologicalComplex _).map φ ≫ (F.mapHomologicalComplex _).map a.right
            rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
            exact congrArg ((F.mapHomologicalComplex _).map) (show a.left ≫ ψ=φ ≫ a.right from a.w))) := by
  rw [← cancel_epi (homotopyCofiber.mapHomologicalComplexObjIso φ F).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply homotopyCofiber.ext_from_X' ((F.mapHomologicalComplex _).map φ) 0
      (by intro h; change _+1=0 at h; omega)
    simp only [comp_f]
    erw [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc]
    erw [← CategoryTheory.Functor.map_comp_assoc,cofiberMap_inr,CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    erw [homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom]
    simp [cofiberMap_inr]
  | succ i =>
    apply homotopyCofiber.ext_from_X ((F.mapHomologicalComplex _).map φ) i (i+1) (natDownStep i)
    · simp only [comp_f]
      erw [homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv_assoc]
      erw [← CategoryTheory.Functor.map_comp_assoc,cofiberMap_inl,CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
      erw [map_inl_cofiberComparison F ψ i]
      simp [cofiberMap_inl]
    · simp only [comp_f]
      erw [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc]
      erw [← CategoryTheory.Functor.map_comp_assoc,cofiberMap_inr,CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
      erw [homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom]
      simp [cofiberMap_inr]

/-- Mapping a cone commutes with a natural transformation, using the same actual cone maps. -/
@[reassoc]
theorem cofiberComparison_naturality (τ : F ⟶ G) (φ : K ⟶ L) :
    (NatTrans.mapHomologicalComplex τ _).app (homotopyCofiber φ) ≫
      (homotopyCofiber.mapHomologicalComplexObjIso φ G).hom =
    (homotopyCofiber.mapHomologicalComplexObjIso φ F).hom ≫
      homotopyCofiber.mapArrowHom ((F.mapHomologicalComplex _).map φ)
        ((G.mapHomologicalComplex _).map φ) (fun j => ⟨j+1,natDownStep j⟩)
        (Arrow.homMk ((NatTrans.mapHomologicalComplex τ _).app K)
          ((NatTrans.mapHomologicalComplex τ _).app L)
          ((NatTrans.mapHomologicalComplex τ _).naturality φ).symm) := by
  rw [← cancel_epi (homotopyCofiber.mapHomologicalComplexObjIso φ F).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply homotopyCofiber.ext_from_X' ((F.mapHomologicalComplex _).map φ) 0
      (by intro h; change _+1=0 at h; omega)
    simp only [comp_f]
    erw [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc]
    change F.map (homotopyCofiber.inrX φ 0) ≫ τ.app _ ≫ _ = _
    rw [τ.naturality_assoc]
    erw [homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom]
    exact (cofiberMap_inr ((F.mapHomologicalComplex _).map φ) ((G.mapHomologicalComplex _).map φ)
      (Arrow.homMk ((NatTrans.mapHomologicalComplex τ _).app K) ((NatTrans.mapHomologicalComplex τ _).app L)
        ((NatTrans.mapHomologicalComplex τ _).naturality φ).symm) 0).symm
  | succ i =>
    apply homotopyCofiber.ext_from_X ((F.mapHomologicalComplex _).map φ) i (i+1) (natDownStep i)
    · simp only [comp_f]
      erw [homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv_assoc]
      change F.map (homotopyCofiber.inlX φ i (i+1) (natDownStep i)) ≫ τ.app _ ≫ _ = _
      rw [τ.naturality_assoc]
      erw [map_inl_cofiberComparison G φ i]
      exact (cofiberMap_inl ((F.mapHomologicalComplex _).map φ) ((G.mapHomologicalComplex _).map φ)
        (Arrow.homMk ((NatTrans.mapHomologicalComplex τ _).app K) ((NatTrans.mapHomologicalComplex τ _).app L)
          ((NatTrans.mapHomologicalComplex τ _).naturality φ).symm) i).symm
    · simp only [comp_f]
      erw [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc]
      change F.map (homotopyCofiber.inrX φ (i+1)) ≫ τ.app _ ≫ _ = _
      rw [τ.naturality_assoc]
      erw [homotopyCofiber.map_inrX_mapHomologicalComplexObjXIso_hom]
      exact (cofiberMap_inr ((F.mapHomologicalComplex _).map φ) ((G.mapHomologicalComplex _).map φ)
        (Arrow.homMk ((NatTrans.mapHomologicalComplex τ _).app K) ((NatTrans.mapHomologicalComplex τ _).app L)
          ((NatTrans.mapHomologicalComplex τ _).naturality φ).symm) (i+1)).symm

end NSP14.Homological
