module
public import NSP14.Homological.KoszulExterior
public import NSP14.Homological.HomogeneousBasisPieces
@[expose] public section
open scoped Classical TensorProduct BigOperators
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Homological
variable (k σ : Type) [Field k] [Fintype σ]

theorem koszulExteriorTensorEquiv_symm_basis_homogeneous
    (M : ModuleCat (VariableRing k σ)) (G : GradedPolynomialModule k σ M) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a∈G.degreeSpace (deg a)) (i : ℕ) (a : J) (w : ⋀[k]^i (σ → k)) :
    (koszulExteriorTensorEquiv k σ M b i).symm (b a ⊗ₜ[k] w)∈
      (koszulChainGrading k σ M G (variableList k σ) i).degreeSpace (deg a) := by
  have he (s : KoszulSlot (variableList k σ).length i) :
      (koszulExteriorTensorEquiv k σ M b i).symm
        (b a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k i s)=
          koszulSlotBasis k σ M b (variableList k σ) i (s,a) := by
    apply (koszulExteriorTensorEquiv k σ M b i).injective
    rw [LinearEquiv.apply_symm_apply,koszulExteriorTensorEquiv_basis]
  rw [← (koszulExteriorBasis (σ:=σ) k i).sum_repr w,TensorProduct.tmul_sum,map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [TensorProduct.tmul_smul,map_smul,he]
  exact Submodule.smul_mem _ _ (koszulSlotBasis_homogeneous k σ M G b deg hb _ i (s,a))

omit [Fintype σ] in
theorem homogeneousBasisMap_degree (M N : ModuleCat (VariableRing k σ))
    (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule k σ N) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a∈G.degreeSpace (deg a))
    (f : coefficientModule k σ M →ₗ[k] coefficientModule k σ N)
    (hfb : ∀ a,f (b a)∈H.degreeSpace (deg a))
    (t : ℤ) (a : coefficientModule k σ M) (ha : a∈G.degreeSpace t) : f a∈H.degreeSpace t := by
  have h : G.degreeSpace t ≤ (H.degreeSpace t).comap f := by
    rw [← homogeneous_basis_span k σ M G b deg hb t]
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change f (b p.val)∈H.degreeSpace t
    simpa only [p.property] using hfb p.val
  exact h ha
end NSP14.Homological
