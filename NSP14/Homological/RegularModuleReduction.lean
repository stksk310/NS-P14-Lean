module
public import NSP14.Homological.RegularElementQuotient
public import NSP14.Homological.FullListBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (r : R) (M : ModuleCat.{u} R)

noncomputable def scalarModuleQuotient : ModuleCat.{u} R :=
  ModuleCat.of R (M ⧸ (r • (𝟙 M)).hom.range)

noncomputable def scalarModuleProjection : M ⟶ scalarModuleQuotient R r M :=
  ModuleCat.ofHom ((r • (𝟙 M)).hom.range.mkQ)

theorem scalarModule_comp : (r • (𝟙 M)) ≫ scalarModuleProjection R r M=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨m,rfl⟩

noncomputable def scalarModuleSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (r • (𝟙 M)) (scalarModuleProjection R r M) (scalarModule_comp R r M)

theorem scalarModuleSequence_shortExact (hr : Function.Injective (fun m : M => r • m)) :
    (scalarModuleSequence R r M).ShortExact := by
  unfold scalarModuleSequence
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  · rw [ModuleCat.mono_iff_injective]
    exact hr
  · rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective _

variable (k : Type u) [Field k] [Algebra k R]

/-- Regular-element reduction for an actual module, including ideals.
The chain groups are allowed to be infinite dimensional over k. -/
noncomputable def regularModuleCoefficientReductionIso (rs : List R)
    (hr : Function.Injective (fun m : M => r • m)) (i : ℕ) :
    (actionCoefficientComplex k R (r::rs) M).homology i ≅
      (actionCoefficientComplex k R rs (scalarModuleQuotient R r M)).homology i := by
  let S := (scalarModuleSequence R r M).map (actionCoefficientFunctor R k rs)
  have hS := actionCoefficientFunctor_shortExact R k rs _ (scalarModuleSequence_shortExact R r M hr)
  exact (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (actionCoefficientConsIso R k r rs M) ≪≫
    monicConeHomologyIso k S hS i

variable (σ : Type u) [Fintype σ]
noncomputable def regularModulePolynomialReductionIso (φ : VariableRing k σ →ₐ[k] R)
    (hr : Function.Injective (fun m : M => r • m)) (i : ℕ) :
    (actionCoefficientComplex k R (r::(variableList k σ).map (fun x => φ (MvPolynomial.X x))) M).homology i ≅
      koszulHomologyK k σ ((ModuleCat.restrictScalars φ.toRingHom).obj (scalarModuleQuotient R r M)) i :=
  regularModuleCoefficientReductionIso R r M k _ hr i ≪≫
    coefficientComplexHomologyIso k (polynomialActionCoefficientIso k R σ φ (variableList k σ) (scalarModuleQuotient R r M)) i ≪≫
      coefficientCanonicalListHomologyIso k σ _ i

noncomputable def actionFullPolynomialHomologyIso (φ : VariableRing k σ →ₐ[k] R)
    (xs : List σ) (hall : ∀ x,x∈xs) (hnodup : xs.Nodup) (i : ℕ) :
    (actionCoefficientComplex k R (xs.map (fun x => φ (MvPolynomial.X x))) M).homology i ≅
      koszulHomologyK k σ ((ModuleCat.restrictScalars φ.toRingHom).obj M) i :=
  coefficientComplexHomologyIso k (polynomialActionCoefficientIso k R σ φ xs M) i ≪≫
    (fullListHomologyKIso k σ xs hall hnodup _ i).symm
end NSP14.Homological
