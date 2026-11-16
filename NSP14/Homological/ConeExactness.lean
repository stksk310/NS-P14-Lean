module

public import NSP14.Homological.KoszulAugmentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u w
variable {R : Type u} [CommRing R]

/-- The concrete positive-degree exactness criterion retains its actual indices. -/
theorem chain_exact_succ_iff (K : ChainComplex (ModuleCat.{w} R) ℕ) (i : ℕ) :
    K.ExactAt (i+1) ↔ ∀ z : K.X (i+1), K.d (i+1) i z=0 →
      ∃ w : K.X (i+2), K.d (i+2) (i+1) w=z := by
  rw [K.exactAt_iff' (i+2) (i+1) i ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  rfl

noncomputable def coneFirst (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) :
    (homotopyCofiber (r • 𝟙 K)).X (i+1) →ₗ[R] K.X i :=
  (homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl).hom

noncomputable def coneSecond (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) :
    (homotopyCofiber (r • 𝟙 K)).X i →ₗ[R] K.X i := (homotopyCofiber.sndX (r • 𝟙 K) i).hom

theorem cone_element_ext (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ)
    (a b : (homotopyCofiber (r • 𝟙 K)).X (i+1))
    (hfirst : coneFirst K r i a=coneFirst K r i b)
    (hsecond : coneSecond K r (i+1) a=coneSecond K r (i+1) b) : a=b := by
  erw [scalarCone_split K r i a,scalarCone_split K r i b]
  rw [show (homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl) a =
      (homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl) b from hfirst,
    show (homotopyCofiber.sndX (r • 𝟙 K) (i+1)) a =
      (homotopyCofiber.sndX (r • 𝟙 K) (i+1)) b from hsecond]

theorem cone_d_first (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ)
    (z : (homotopyCofiber (r • 𝟙 K)).X (i+2)) :
    coneFirst K r i ((homotopyCofiber (r • 𝟙 K)).d (i+2) (i+1) z) =
      -K.d (i+1) i (coneFirst K r (i+1) z) := by
  have he := congrArg (fun f => f.hom z) (homotopyCofiber.d_fstX (r • 𝟙 K) (i+2) (i+1) i rfl rfl)
  exact he

theorem cone_d_second (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ)
    (z : (homotopyCofiber (r • 𝟙 K)).X (i+1)) :
    coneSecond K r i ((homotopyCofiber (r • 𝟙 K)).d (i+1) i z) =
      r • coneFirst K r i z + K.d (i+1) i (coneSecond K r (i+1) z) := by
  have he := congrArg (fun f => f.hom z) (homotopyCofiber.d_sndX (r • 𝟙 K) (i+1) i rfl)
  exact he

theorem coneFirst_inl (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) (a : K.X i) :
    coneFirst K r i (homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl a)=a :=
  congrArg (fun f : K.X i ⟶ K.X i => f.hom a) (homotopyCofiber.inlX_fstX (r • 𝟙 K) i (i+1) rfl)

theorem coneFirst_inr (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) (b : K.X (i+1)) :
    coneFirst K r i (homotopyCofiber.inrX (r • 𝟙 K) (i+1) b)=0 :=
  congrArg (fun f : K.X (i+1) ⟶ K.X i => f.hom b) (homotopyCofiber.inrX_fstX (r • 𝟙 K) (i+1) i rfl)

theorem coneSecond_inl (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) (a : K.X i) :
    coneSecond K r (i+1) (homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl a)=0 :=
  congrArg (fun f : K.X i ⟶ K.X (i+1) => f.hom a) (homotopyCofiber.inlX_sndX (r • 𝟙 K) i (i+1) rfl)

theorem coneSecond_inr (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) (b : K.X i) :
    coneSecond K r i (homotopyCofiber.inrX (r • 𝟙 K) i b)=b :=
  congrArg (fun f : K.X i ⟶ K.X i => f.hom b) (homotopyCofiber.inrX_sndX (r • 𝟙 K) i)

/-- A regular scalar on H₀ and positive-degree exactness imply exactness of its scalar cone. -/
theorem scalarCone_exact_positive (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R)
    (hK : ∀ i, K.ExactAt (i+1))
    (hregular : ∀ a : K.X 0, r • a ∈ (K.d 1 0).hom.range → a ∈ (K.d 1 0).hom.range) :
    ∀ i, (homotopyCofiber (r • 𝟙 K)).ExactAt (i+1) := by
  intro i
  rw [chain_exact_succ_iff]
  intro z hz
  let a := coneFirst K r i z
  let b := coneSecond K r (i+1) z
  have hcycle : r • a + K.d (i+1) i b=0 := by
    have he := cone_d_second K r i z
    rw [hz,map_zero] at he
    exact he.symm
  have ha : a ∈ (K.d (i+1) i).hom.range := by
    cases i with
    | zero =>
      apply hregular
      refine ⟨-b,?_⟩
      change K.d 1 0 (-b)=r • a
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_left hcycle
    | succ i =>
      have he := cone_d_first K r i z
      rw [hz,map_zero] at he
      have hda : K.d (i+1) i a=0 := neg_eq_zero.mp he.symm
      exact (chain_exact_succ_iff K i).1 (hK i) a hda
  obtain ⟨c,hc⟩ := ha
  have hb : K.d (i+1) i (b+r • c)=0 := by
    rw [map_add,map_smul,hc]
    exact (add_comm _ _).trans hcycle
  obtain ⟨e,he⟩ := (chain_exact_succ_iff K i).1 (hK i) (b+r • c) hb
  let w := homotopyCofiber.inlX (r • 𝟙 K) (i+1) (i+2) rfl (-c) + homotopyCofiber.inrX (r • 𝟙 K) (i+2) e
  refine ⟨w,?_⟩
  apply cone_element_ext K r i
  · rw [cone_d_first]
    have hw : coneFirst K r (i+1) w = -c := by
      dsimp only [w]
      erw [map_add,coneFirst_inl,coneFirst_inr,add_zero]
    rw [hw,map_neg,neg_neg]
    exact hc
  · rw [cone_d_second]
    have hw1 : coneFirst K r (i+1) w = -c := by
      dsimp only [w]
      erw [map_add,coneFirst_inl,coneFirst_inr,add_zero]
    have hw2 : coneSecond K r (i+2) w=e := by
      dsimp only [w]
      erw [map_add,coneSecond_inl,coneSecond_inr,zero_add]
    rw [hw1,hw2,he,smul_neg]
    dsimp [b]
    abel

end NSP14.Homological
