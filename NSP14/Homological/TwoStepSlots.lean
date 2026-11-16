module
public import NSP14.Homological.CoefficientSlotsEquiv
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
variable (C U : Type u) [AddCommGroup C] [Module k C] [AddCommGroup U] [Module k U]
  (e : coefficientModule k σ M ≃ₗ[k] (C × U))

noncomputable def twoStepSlotsEquiv (xs : List σ) (j : ℕ) :
    ((coefficientKoszulListFunctor k σ xs).obj M).X j ≃ₗ[k]
      ((KoszulSlot xs.length j → C) × (KoszulSlot xs.length j → U)) where
  toFun a :=
    (fun s => (e (coefficientSlotsEquiv k σ M xs j a s)).1,
     fun s => (e (coefficientSlotsEquiv k σ M xs j a s)).2)
  invFun p := (coefficientSlotsEquiv k σ M xs j).symm (fun s => e.symm (p.1 s,p.2 s))
  left_inv a := by
    apply (coefficientSlotsEquiv k σ M xs j).injective
    simp only [Prod.eta,LinearEquiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext <;> funext s <;> simp only [LinearEquiv.apply_symm_apply]
  map_add' a b := by
    apply Prod.ext <;> funext s <;> simp only [map_add,Prod.fst_add,Prod.snd_add,Pi.add_apply]
  map_smul' c a := by
    apply Prod.ext <;> funext s <;> simp only [map_smul,Pi.smul_apply,RingHom.id_apply] <;> rfl

noncomputable def twoStepLowerProjection (xs : List σ) (j : ℕ) :
    ((coefficientKoszulListFunctor k σ xs).obj M).X j →ₗ[k] (KoszulSlot xs.length j → C) :=
  (LinearMap.fst k _ _).comp (twoStepSlotsEquiv k σ M C U e xs j).toLinearMap

noncomputable def twoStepUpperInclusion (xs : List σ) (j : ℕ) :
    (KoszulSlot xs.length j → U) →ₗ[k] ((coefficientKoszulListFunctor k σ xs).obj M).X j :=
  (twoStepSlotsEquiv k σ M C U e xs j).symm.toLinearMap.comp (LinearMap.inr k _ _)

theorem twoStepLowerProjection_surjective (xs : List σ) (j : ℕ) :
    Function.Surjective (twoStepLowerProjection k σ M C U e xs j) := by
  intro a
  refine ⟨(twoStepSlotsEquiv k σ M C U e xs j).symm (a,0),?_⟩
  change ((twoStepSlotsEquiv k σ M C U e xs j)
    ((twoStepSlotsEquiv k σ M C U e xs j).symm (a,0))).1=a
  rw [LinearEquiv.apply_symm_apply]

theorem twoStepUpperInclusion_injective (xs : List σ) (j : ℕ) :
    Function.Injective (twoStepUpperInclusion k σ M C U e xs j) :=
  (twoStepSlotsEquiv k σ M C U e xs j).symm.injective.comp (fun _ _ h => congrArg Prod.snd h)

theorem twoStepSlotsEquiv_upper (xs : List σ) (j : ℕ) (f : KoszulSlot xs.length j → U) :
    twoStepSlotsEquiv k σ M C U e xs j (twoStepUpperInclusion k σ M C U e xs j f)=(0,f) :=
  (twoStepSlotsEquiv k σ M C U e xs j).apply_symm_apply (0,f)

theorem finiteSum_fst {I : Type*} [Fintype I] (f : I → C × U) :
    (∑ i,f i).1=∑ i,(f i).1 := map_sum (AddMonoidHom.fst C U) f Finset.univ

theorem finiteSum_snd {I : Type*} [Fintype I] (f : I → C × U) :
    (∑ i,f i).2=∑ i,(f i).2 := map_sum (AddMonoidHom.snd C U) f Finset.univ
end NSP14.Homological
