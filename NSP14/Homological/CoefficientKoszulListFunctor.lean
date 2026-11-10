module
public import NSP14.Homological.CoefficientKoszulFunctor
public import NSP14.Homological.PolynomialRestrictionKoszul
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]

/-- An arbitrary list, with no claim of finite homology when variables
have been omitted. -/
noncomputable def coefficientKoszulListFunctor (xs : List σ) :
    ModuleCat.{u} (VariableRing k σ) ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  koszulFunctor k σ xs ⋙
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex (ComplexShape.down ℕ)

noncomputable instance coefficientKoszulListFunctor_additive (xs : List σ) :
    (coefficientKoszulListFunctor k σ xs).Additive := by
  unfold coefficientKoszulListFunctor
  infer_instance

theorem coefficientKoszulListFunctor_shortExact (xs : List σ)
    (S : ShortComplex (ModuleCat.{u} (VariableRing k σ))) (hS : S.ShortExact) :
    (S.map (coefficientKoszulListFunctor k σ xs)).ShortExact := by
  have hK := koszul_shortExact k σ xs S hS
  let : Mono (S.map (koszulFunctor k σ xs)).f := hK.mono_f
  let : Epi (S.map (koszulFunctor k σ xs)).g := hK.epi_g
  exact hK.map ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _)

theorem coefficientKoszulListFunctor_full [Fintype σ] :
    coefficientKoszulListFunctor k σ (variableList k σ)=coefficientKoszulFunctor k σ := rfl

noncomputable instance coefficientKoszulListFunctor_full_homologyFinite [Fintype σ]
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.Finite k (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).homology i) := by
  rw [coefficientKoszulListFunctor_full]
  infer_instance

variable (τ : Type u) (φ : VariableRing k τ →ₐ[k] VariableRing k σ) (v : τ → σ)
  (hφ : ∀ t,φ (MvPolynomial.X t)=MvPolynomial.X (v t))

noncomputable def coefficientRestrictionKoszulIso (xs : List τ) (M : ModuleCat.{u} (VariableRing k σ)) :
    (coefficientKoszulListFunctor k σ (xs.map v)).obj M ≅
      (coefficientKoszulListFunctor k τ xs).obj ((ModuleCat.restrictScalars φ.toRingHom).obj M) :=
  (restrictedCoefficientComplexIso k τ σ φ (koszulList k σ (xs.map v) M)).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap k (VariableRing k τ))).mapHomologicalComplex _).mapIso
      (polynomialRestrictionKoszulIso k τ σ φ v hφ xs M)

noncomputable def coefficientRestrictionKoszulModuleIso (xs : List τ)
    (M : ModuleCat.{u} (VariableRing k σ)) (N : ModuleCat.{u} (VariableRing k τ))
    (e : (ModuleCat.restrictScalars φ.toRingHom).obj M ≅ N) :
    (coefficientKoszulListFunctor k σ (xs.map v)).obj M ≅
      (coefficientKoszulListFunctor k τ xs).obj N :=
  coefficientRestrictionKoszulIso k σ τ φ v hφ xs M ≪≫
    (coefficientKoszulListFunctor k τ xs).mapIso e

theorem complex_homologyFinite_of_iso
    {K J : ChainComplex (ModuleCat.{u} k) ℕ} (e : K ≅ J) (i : ℕ)
    [Module.Finite k (J.homology i)] : Module.Finite k (K.homology i) := by
  let eH : K.homology i ≅ J.homology i :=
    (homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso e
  exact Module.Finite.equiv eH.symm.toLinearEquiv

theorem shortExact_map_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (G : D ⥤ E) [G.PreservesZeroMorphisms]
    (S : ShortComplex C) (h : ((S.map F).map G).ShortExact) :
    (S.map (F ⋙ G)).ShortExact := by
  rw [ShortComplex.map_comp]
  exact h
end NSP14.Homological
