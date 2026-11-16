module

public import NSP14.Homological.FreeKoszulHomology

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable {R : Type u} [CommRing R]

theorem chain_h0_map_zero_of_boundaries {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (hf : ∀ x : K.X 0, f.f 0 x ∈ (L.d 1 0).hom.range) : homologyMap f 0=0 := by
  have hz : f.f 0 ≫ L.pOpcycles 0=0 := by
    apply ModuleCat.hom_ext
    ext x
    change (L.sc 0).pOpcycles (f.f 0 x)=0
    apply (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (L.sc 0) _).mpr
    have he : (ComplexShape.down ℕ).prev 0=1 := by simp
    change f.f 0 x ∈ (L.d ((ComplexShape.down ℕ).prev 0) 0).hom.range
    rw [he]
    exact hf x
  have ho : opcyclesMap f 0=0 := by
    rw [← cancel_epi (K.pOpcycles 0),p_opcyclesMap,hz,comp_zero]
  rw [← cancel_mono (L.homologyι 0),homologyι_naturality,ho,comp_zero,zero_comp]

variable (k σ : Type u) [Field k]

@[reassoc]
theorem koszulZeroIso_naturality (xs : List σ) {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) :
    ((koszulFunctor k σ xs).map f).f 0 ≫ (koszulZeroIso k σ xs N).hom =
      (koszulZeroIso k σ xs M).hom ≫ f := by
  induction xs with
  | nil => simp [koszulFunctor,koszulMap,koszulZeroIso]
  | cons x xs ih =>
    let : IsIso (homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0) := by
      have hn : ¬(ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
        intro h; change _+1=0 at h; omega
      simpa only [homotopyCofiber.inrX,dite_eq_right hn] using
        (inferInstanceAs (IsIso (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).inv))
    rw [← cancel_epi (homotopyCofiber.inrX
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0)]
    change homotopyCofiber.inrX
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 ≫
      ((scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).map
      ((koszulFunctor k σ xs).map f)).f 0 ≫ _ = _
    erw [scalarCone_map_inr_assoc,koszulZeroIso_cons_inr,← Category.assoc,koszulZeroIso_cons_inr,ih]

theorem koszul_boundary_zero_iff (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    (a : (koszulList k σ xs M).X 0) :
    a ∈ ((koszulList k σ xs M).d 1 0).hom.range ↔
      (koszulZeroIso k σ xs M).hom a ∈ koszulVariableSubmodule k σ xs M := by
  rw [← koszul_zero_boundary]
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨z,rfl⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,(koszulZeroIso k σ xs M).toLinearEquiv.injective hz⟩

/-- The usual minimality condition (image in the variables times N) kills the H₀-map. -/
theorem koszul_h0_map_zero_of_minimal (xs : List σ)
    {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N)
    (hf : ∀ m : M,f m∈koszulVariableSubmodule k σ xs N) :
    (koszulHomologyFunctor k σ xs 0).map f=0 := by
  apply chain_h0_map_zero_of_boundaries
  intro a
  apply (koszul_boundary_zero_iff k σ xs N _).mpr
  have he := congrArg (fun g => g.hom a) (koszulZeroIso_naturality k σ xs f)
  change (koszulZeroIso k σ xs N).hom (((koszulFunctor k σ xs).map f).f 0 a) ∈ _
  exact he.symm ▸ hf ((koszulZeroIso k σ xs M).hom a)

end NSP14.Homological
