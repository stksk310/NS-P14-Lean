module

public import NSP14.Homological.KoszulLowDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

namespace NSP14.Homological

universe u v w
variable (k : Type u) (σ : Type v) [CommRing k]

noncomputable def koszulVariableSubmodule (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    Submodule (VariableRing k σ) M :=
  match xs with
  | [] => ⊥
  | x::xs => (variableOperator k σ M x).range ⊔ koszulVariableSubmodule xs M

theorem koszulZeroIso_cons_inr (x : σ) (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 ≫
      (koszulZeroIso k σ (x::xs) M).hom = (koszulZeroIso k σ xs M).hom := by
  have hn : ¬(ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
    intro h; change (ComplexShape.down ℕ).next 0+1=0 at h; omega
  simp only [homotopyCofiber.inrX,dite_eq_right hn]
  change (homotopyCofiber.XIso ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 hn).inv ≫
    (homotopyCofiber.XIso ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 hn).hom ≫
      (koszulZeroIso k σ xs M).hom = _
  exact Iso.inv_hom_id_assoc _ _

theorem koszulZeroDifferential_cons_left (x : σ) (xs : List σ)
    (M : ModuleCat.{w} (VariableRing k σ)) (a : (koszulList k σ xs M).X 0) :
    koszulZeroDifferential k σ (x::xs) M
      (homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 1 rfl a) =
      (MvPolynomial.X x : VariableRing k σ) • (koszulZeroIso k σ xs M).hom a := by
  have hn : ¬(ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
    intro h; change (ComplexShape.down ℕ).next 0+1=0 at h; omega
  change (homotopyCofiber.inlX _ 0 1 rfl ≫ (koszulList k σ (x::xs) M).d 1 0 ≫
    (koszulZeroIso k σ (x::xs) M).hom) a = _
  erw [homotopyCofiber.inlX_d'_assoc _ 1 0 rfl hn,koszulZeroIso_cons_inr]
  exact map_smul ((koszulZeroIso k σ xs M).hom.hom) _ a

theorem koszulZeroDifferential_cons_right (x : σ) (xs : List σ)
    (M : ModuleCat.{w} (VariableRing k σ)) (b : (koszulList k σ xs M).X 1) :
    koszulZeroDifferential k σ (x::xs) M
      (homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 1 b) =
      koszulZeroDifferential k σ xs M b := by
  change (homotopyCofiber.inrX _ 1 ≫ (koszulList k σ (x::xs) M).d 1 0 ≫
    (koszulZeroIso k σ (x::xs) M).hom) b = _
  erw [homotopyCofiber.inrX_d_assoc,koszulZeroIso_cons_inr]
  rfl

/-- Every element splits into its actual two subset-recursion components. -/
theorem scalarCone_split {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{w} R) ℕ)
    (r : R) (i : ℕ) (z : (homotopyCofiber (r • 𝟙 K)).X (i+1)) :
    z = homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl (homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl z) +
      homotopyCofiber.inrX (r • 𝟙 K) (i+1) (homotopyCofiber.sndX (r • 𝟙 K) (i+1) z) := by
  have he : homotopyCofiber.fstX (r • 𝟙 K) (i+1) i rfl ≫ homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl +
      homotopyCofiber.sndX (r • 𝟙 K) (i+1) ≫ homotopyCofiber.inrX (r • 𝟙 K) (i+1) = 𝟙 _ := by
    apply homotopyCofiber.ext_to_X (r • 𝟙 K) (i+1) i rfl
    · simp only [Category.assoc,Preadditive.add_comp,Category.id_comp]
      erw [homotopyCofiber.inlX_fstX _ i (i+1) rfl,
        homotopyCofiber.inrX_fstX _ (i+1) i rfl]
      simp
    · simp only [Category.assoc,Preadditive.add_comp,Category.id_comp]
      erw [homotopyCofiber.inlX_sndX _ i (i+1) rfl,
        homotopyCofiber.inrX_sndX]
      simp
  exact (congrArg (fun f => f z) he).symm

theorem koszul_zero_boundary (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    (koszulZeroDifferential k σ xs M).range=koszulVariableSubmodule k σ xs M := by
  induction xs with
  | nil =>
    have hz : koszulZeroDifferential k σ [] M=0 := by
      ext z
      have : Subsingleton ((koszulList k σ [] M).X 1) := ModuleCat.subsingleton_of_isZero
        (koszul_piece_isZero_of_gt k σ [] M 1 (by simp))
      have he : z=0 := Subsingleton.elim _ _
      rw [he,map_zero,LinearMap.zero_apply]
    rw [hz,LinearMap.range_zero]
    rfl
  | cons x xs ih =>
    change (koszulZeroDifferential k σ (x::xs) M).range =
      (variableOperator k σ M x).range ⊔ koszulVariableSubmodule k σ xs M
    rw [← ih]
    apply le_antisymm
    · rintro a ⟨z,rfl⟩
      erw [scalarCone_split (koszulList k σ xs M) (MvPolynomial.X x) 0 z,map_add,
        koszulZeroDifferential_cons_left,koszulZeroDifferential_cons_right]
      apply Submodule.add_mem_sup
      · exact ⟨_,rfl⟩
      · exact ⟨_,rfl⟩
    · apply sup_le
      · rintro a ⟨b,rfl⟩
        refine ⟨homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 1 rfl
          ((koszulZeroIso k σ xs M).inv b),?_⟩
        rw [koszulZeroDifferential_cons_left]
        change (MvPolynomial.X x : VariableRing k σ) •
          ((koszulZeroIso k σ xs M).hom ((koszulZeroIso k σ xs M).inv b)) = (MvPolynomial.X x : VariableRing k σ) • b
        congr 1
        exact congrArg (fun f : M ⟶ M => f.hom b) (koszulZeroIso k σ xs M).inv_hom_id
      · rintro a ⟨b,rfl⟩
        exact ⟨homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 1 b,
          koszulZeroDifferential_cons_right k σ x xs M b⟩

/-- H₀ is the module modulo the submodule generated by the actual variable actions. -/
noncomputable def koszulH0Equiv (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    koszulHomology k σ xs M 0 ≃ₗ[VariableRing k σ] (M ⧸ koszulVariableSubmodule k σ xs M) :=
  (koszulH0BoundaryEquiv k σ xs M).trans
    (Submodule.quotEquivOfEq _ _ (koszul_zero_boundary k σ xs M))

end NSP14.Homological
