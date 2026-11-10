module

public import NSP14.Homological.ConeExactness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u w
theorem natDownStep (i : ℕ) : (ComplexShape.down ℕ).Rel (i+1) i := rfl

variable (R : Type u) [CommRing R] (r : R)
variable {K L : ChainComplex (ModuleCat.{w} R) ℕ}

@[reassoc (attr := simp)]
theorem scalarCone_map_inr (f : K ⟶ L) (i : ℕ) :
    homotopyCofiber.inrX (r • 𝟙 K) i ≫ ((scalarConeFunctor R r).map f).f i =
      f.f i ≫ homotopyCofiber.inrX (r • 𝟙 L) i := by
  simp [scalarConeFunctor,homotopyCofiber.mapArrowHom]

@[reassoc (attr := simp)]
theorem scalarCone_map_inl (f : K ⟶ L) (i : ℕ) :
    homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl ≫ ((scalarConeFunctor R r).map f).f (i+1) =
      f.f i ≫ homotopyCofiber.inlX (r • 𝟙 L) i (i+1) rfl := by
  change homotopyCofiber.inlX _ i (i+1) rfl ≫ (homotopyCofiber.desc _ _ _).f (i+1) = _
  erw [homotopyCofiber.inlX_desc_f _ _ _ i (i+1) rfl]
  simp [homotopyCofiber.inrCompHomotopy_hom]

@[reassoc (attr := simp)]
theorem scalarCone_map_fst (f : K ⟶ L) (i : ℕ) :
    ((scalarConeFunctor R r).map f).f (i+1) ≫ homotopyCofiber.fstX (r • 𝟙 L) (i+1) i rfl =
      homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl ≫ f.f i := by
  apply homotopyCofiber.ext_from_X (r • 𝟙 K) i (i+1) rfl
  · simp
  · simp

@[reassoc (attr := simp)]
theorem scalarCone_map_snd (f : K ⟶ L) (i : ℕ) :
    ((scalarConeFunctor R r).map f).f i ≫ homotopyCofiber.sndX (r • 𝟙 L) i =
      homotopyCofiber.sndX (r • 𝟙 K) i ≫ f.f i := by
  cases i with
  | zero =>
    apply homotopyCofiber.ext_from_X' (r • 𝟙 K) 0 (by intro h; change _+1=0 at h; omega)
    simp
  | succ i =>
    apply homotopyCofiber.ext_from_X (r • 𝟙 K) i (i+1) rfl
    · simp
    · simp

noncomputable instance scalarConeFunctor_additive : (scalarConeFunctor.{u,w} R r).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply homotopyCofiber.ext_from_X' (r • 𝟙 K) 0 (by intro h; change _+1=0 at h; omega)
      simp [Preadditive.comp_add]
    | succ i =>
      apply homotopyCofiber.ext_from_X (r • 𝟙 K) i (i+1) rfl
      · simp [Preadditive.comp_add]
      · simp [Preadditive.comp_add]

noncomputable instance koszulFunctor_additive (k : Type u) (σ : Type*) [CommRing k] (xs : List σ) :
    (koszulFunctor k σ xs).Additive := by
  induction xs with
  | nil => exact inferInstanceAs ((ChainComplex.single₀ _).Additive)
  | cons x xs ih =>
    change (koszulFunctor k σ xs ⋙ scalarConeFunctor _ (MvPolynomial.X x)).Additive
    infer_instance

noncomputable instance koszulHomologyFunctor_additive (k : Type u) (σ : Type*) [CommRing k]
    (xs : List σ) (i : ℕ) : (koszulHomologyFunctor k σ xs i).Additive :=
  inferInstanceAs ((koszulFunctor k σ xs ⋙ homologyFunctor _ (ComplexShape.down ℕ) i).Additive)

end NSP14.Homological
