module

public import NSP14.Homological.MinimalFreeTower

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable def principalModule (f : VariableRing k σ) : ModuleCat.{u} (VariableRing k σ) :=
  ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ Ideal.span {f})

noncomputable def principalMultiply (f : VariableRing k σ) :
    ModuleCat.of (VariableRing k σ) (VariableRing k σ) ⟶
      ModuleCat.of (VariableRing k σ) (VariableRing k σ) :=
  ModuleCat.ofHom (LinearMap.mulLeft (VariableRing k σ) f)

noncomputable def principalProjection (f : VariableRing k σ) :
    ModuleCat.of (VariableRing k σ) (VariableRing k σ) ⟶ principalModule k σ f :=
  ModuleCat.ofHom (Y := principalModule k σ f) (Ideal.span {f}).mkQ

omit [Fintype σ] in
theorem principal_zero (f : VariableRing k σ) : principalMultiply k σ f ≫ principalProjection k σ f=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (Submodule.Quotient.mk (f*a) : (VariableRing k σ) ⧸ Ideal.span {f})=0
  rw [Submodule.Quotient.mk_eq_zero,Ideal.mem_span_singleton]
  exact ⟨a,rfl⟩

noncomputable def principalSequence (f : VariableRing k σ) : ShortComplex (ModuleCat.{u} (VariableRing k σ)) :=
  ShortComplex.mk _ _ (principal_zero k σ f)

omit [Fintype σ] in
theorem principal_shortExact (f : VariableRing k σ) (hf : f≠0) :
    (principalSequence k σ f).ShortExact where
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun a : VariableRing k σ => f*a)
    exact mul_right_injective₀ hf
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    change (Submodule.Quotient.mk a : (VariableRing k σ) ⧸ Ideal.span {f})=0 at ha
    rw [Submodule.Quotient.mk_eq_zero,Ideal.mem_span_singleton] at ha
    obtain ⟨b,hb⟩ := ha
    exact ⟨b,hb.symm⟩

noncomputable instance principal_finite (f : VariableRing k σ) : Module.Finite (VariableRing k σ) (principalModule k σ f) :=
  Module.Finite.of_surjective (principalProjection k σ f).hom (Submodule.mkQ_surjective _)

theorem principal_h0_multiply_zero (f : VariableRing k σ)
    (hf : f∈variablesIdeal k σ (variableList k σ)) :
    (koszulHomologyFunctor k σ (variableList k σ) 0).map (principalMultiply k σ f)=0 := by
  apply koszul_h0_map_zero_of_minimal
  intro a
  rw [polynomial_variable_submodule]
  change f*a∈variablesIdeal k σ (variableList k σ)
  exact Ideal.mul_mem_right _ _ hf

noncomputable def principalH0Iso (f : VariableRing k σ) (hf : f≠0)
    (hm : f∈variablesIdeal k σ (variableList k σ)) :
    koszulHomology k σ (variableList k σ) (principalModule k σ f) 0 ≅
      koszulHomology k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0 := by
  let hS := koszul_shortExact k σ (variableList k σ) (principalSequence k σ f) (principal_shortExact k σ f hf)
  let g := (koszulHomologyFunctor k σ (variableList k σ) 0).map (principalProjection k σ f)
  letI : Mono g := (hS.homology_exact₂ 0).mono_g_iff.mpr (principal_h0_multiply_zero k σ f hm)
  let : Epi ((koszulFunctor k σ (variableList k σ)).map (principalProjection k σ f)) := hS.epi_g
  letI : Epi g := epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j h; change j+1=0 at h; omega)
  letI := isIso_of_mono_of_epi g
  exact (asIso g).symm

noncomputable def principalH1Iso (f : VariableRing k σ) (hf : f≠0)
    (hm : f∈variablesIdeal k σ (variableList k σ)) :
    koszulHomology k σ (variableList k σ) (principalModule k σ f) 1 ≅
      koszulHomology k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0 := by
  let hS := koszul_shortExact k σ (variableList k σ) (principalSequence k σ f) (principal_shortExact k σ f hf)
  let d := hS.δ 1 0 rfl
  letI : Mono d := hS.mono_δ _ _ rfl (freeKoszulHomology_positive k σ
    (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0)
  letI : Epi d := (hS.homology_exact₁ 1 0 rfl).epi_f_iff.mpr (principal_h0_multiply_zero k σ f hm)
  letI := isIso_of_mono_of_epi d
  exact asIso d

theorem principal_totalBetti (f : VariableRing k σ) (hf : f≠0)
    (hm : f∈variablesIdeal k σ (variableList k σ)) :
    totalBetti k σ (principalModule k σ f) 0=1 ∧ totalBetti k σ (principalModule k σ f) 1=1 := by
  constructor
  · exact ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
      (principalH0Iso k σ f hf hm)).toLinearEquiv.finrank_eq.trans (totalBetti_free_zero k σ)
  · exact ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
      (principalH1Iso k σ f hf hm)).toLinearEquiv.finrank_eq.trans (totalBetti_free_zero k σ)

end NSP14.Homological
