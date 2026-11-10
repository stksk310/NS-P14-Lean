module
public import NSP14.Homological.ModuleProducts
public import Mathlib.CategoryTheory.Preadditive.Comma
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R]

noncomputable def arrowConeFunctor :
    Arrow (ChainComplex (ModuleCat.{w} R) ℕ) ⥤ ChainComplex (ModuleCat.{w} R) ℕ where
  obj a := homotopyCofiber a.hom
  map {a b} f := homotopyCofiber.mapArrowHom a.hom b.hom (fun j => ⟨j+1,rfl⟩) f
  map_id _a := homotopyCofiber.mapArrowHom_id _ _
  map_comp f g := homotopyCofiber.mapArrowHom_comp _ _ _ _ f g

variable {A B : Arrow (ChainComplex (ModuleCat.{w} R) ℕ)}

@[reassoc (attr := simp)]
theorem arrowCone_map_inr (f : A ⟶ B) (i : ℕ) :
    homotopyCofiber.inrX A.hom i ≫ ((arrowConeFunctor R).map f).f i =
      f.right.f i ≫ homotopyCofiber.inrX B.hom i := by
  simp [arrowConeFunctor,homotopyCofiber.mapArrowHom]

@[reassoc (attr := simp)]
theorem arrowCone_map_inl (f : A ⟶ B) (i : ℕ) :
    homotopyCofiber.inlX A.hom i (i+1) (natDownStep i) ≫ ((arrowConeFunctor R).map f).f (i+1) =
      f.left.f i ≫ homotopyCofiber.inlX B.hom i (i+1) (natDownStep i) := by
  change homotopyCofiber.inlX _ i (i+1) _ ≫ (homotopyCofiber.desc _ _ _).f (i+1)=_
  erw [homotopyCofiber.inlX_desc_f _ _ _ i (i+1) (natDownStep i)]
  simp [homotopyCofiber.inrCompHomotopy_hom]

@[reassoc (attr := simp)]
theorem arrowCone_map_fst (f : A ⟶ B) (i : ℕ) :
    ((arrowConeFunctor R).map f).f (i+1) ≫ homotopyCofiber.fstX B.hom (i+1) i (natDownStep i) =
      homotopyCofiber.fstX A.hom (i+1) i (natDownStep i) ≫ f.left.f i := by
  apply homotopyCofiber.ext_from_X A.hom i (i+1) (natDownStep i) <;> simp

@[reassoc (attr := simp)]
theorem arrowCone_map_snd (f : A ⟶ B) (i : ℕ) :
    ((arrowConeFunctor R).map f).f i ≫ homotopyCofiber.sndX B.hom i =
      homotopyCofiber.sndX A.hom i ≫ f.right.f i := by
  cases i with
  | zero =>
    apply homotopyCofiber.ext_from_X' A.hom 0 (by intro h;change _+1=0 at h;omega)
    simp
  | succ i =>
    apply homotopyCofiber.ext_from_X A.hom i (i+1) (natDownStep i) <;> simp

noncomputable instance arrowConeFunctor_preservesZero : (arrowConeFunctor.{u,w} R).PreservesZeroMorphisms where
  map_zero A B := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply homotopyCofiber.ext_from_X' A.hom 0 (by intro h;change _+1=0 at h;omega)
      simp
    | succ i =>
      apply homotopyCofiber.ext_from_X A.hom i (i+1) (natDownStep i) <;> simp

variable {K L : ChainComplex (ModuleCat.{w} R) ℕ} (f : K ⟶ L)

theorem arrowCone_split (i : ℕ) (a : (homotopyCofiber f).X (i+1)) :
    a=homotopyCofiber.inlX f i (i+1) (natDownStep i)
        (homotopyCofiber.fstX f (i+1) i (natDownStep i) a)+
      homotopyCofiber.inrX f (i+1) (homotopyCofiber.sndX f (i+1) a) := by
  have he : homotopyCofiber.fstX f (i+1) i (natDownStep i) ≫
        homotopyCofiber.inlX f i (i+1) (natDownStep i)+
      homotopyCofiber.sndX f (i+1) ≫ homotopyCofiber.inrX f (i+1)=𝟙 _ := by
    apply homotopyCofiber.ext_to_X f (i+1) i (natDownStep i) <;>
      simp [Preadditive.add_comp]
  exact (congrArg (fun g => g.hom a) he).symm

noncomputable def arrowConePieceEquiv (i : ℕ) :
    (homotopyCofiber f).X (i+1) ≃ₗ[R] K.X i × L.X (i+1) where
  toLinearMap := (homotopyCofiber.fstX f (i+1) i (natDownStep i)).hom.prod
    (homotopyCofiber.sndX f (i+1)).hom
  invFun a := homotopyCofiber.inlX f i (i+1) (natDownStep i) a.1+
    homotopyCofiber.inrX f (i+1) a.2
  left_inv a := (arrowCone_split R f i a).symm
  right_inv a := by
    apply Prod.ext
    · change (homotopyCofiber.fstX f (i+1) i (natDownStep i)).hom (_+_)=a.1
      rw [map_add]
      change (homotopyCofiber.inlX f i (i+1) (natDownStep i) ≫
        homotopyCofiber.fstX f (i+1) i (natDownStep i)).hom a.1+
        (homotopyCofiber.inrX f (i+1) ≫ homotopyCofiber.fstX f (i+1) i (natDownStep i)).hom a.2=a.1
      rw [homotopyCofiber.inlX_fstX,homotopyCofiber.inrX_fstX]
      simp
    · change (homotopyCofiber.sndX f (i+1)).hom (_+_)=a.2
      rw [map_add]
      change (homotopyCofiber.inlX f i (i+1) (natDownStep i) ≫
        homotopyCofiber.sndX f (i+1)).hom a.1+
        (homotopyCofiber.inrX f (i+1) ≫ homotopyCofiber.sndX f (i+1)).hom a.2=a.2
      rw [homotopyCofiber.inlX_sndX,homotopyCofiber.inrX_sndX]
      simp

noncomputable def arrowConeZeroIso : (homotopyCofiber f).X 0 ≅ L.X 0 :=
  homotopyCofiber.XIso f 0 (by intro h;change _+1=0 at h;omega)
end NSP14.Homological
