module
public import NSP14.Homological.KoszulCoefficientSlots
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped BigOperators Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

theorem coefficientSlotIn_Out (xs : List σ) (j : ℕ) (s t : KoszulSlot xs.length j)
    (a : coefficientModule k σ M) :
    coefficientSlotOut k σ M xs j t (coefficientSlotIn k σ M xs j s a)=
      if s=t then a else 0 := by
  change (koszulSlotOut k σ M xs j t).hom ((koszulSlotIn k σ M xs j s).hom a)=if s=t then a else 0
  have h := congrArg (fun f => f.hom a) (koszulSlotIn_Out k σ M xs j s t)
  by_cases he : s=t
  · subst t
    simpa only [ite_true,ModuleCat.hom_comp,LinearMap.comp_apply,ModuleCat.hom_id,LinearMap.id_apply] using h
  · simpa only [he,ite_false,ModuleCat.hom_comp,LinearMap.comp_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using h

noncomputable def coefficientSlotsEquiv (xs : List σ) (j : ℕ) :
    ((coefficientKoszulListFunctor k σ xs).obj M).X j ≃ₗ[k]
      (KoszulSlot xs.length j → coefficientModule k σ M) where
  toFun a s := coefficientSlotOut k σ M xs j s a
  invFun f := ∑ s,coefficientSlotIn k σ M xs j s (f s)
  left_inv a := (coefficientSlot_decompose k σ M xs j a).symm
  right_inv f := by
    funext t
    simp only [map_sum,coefficientSlotIn_Out]
    simp
  map_add' a b := by funext s;exact map_add _ _ _
  map_smul' c a := by funext s;exact map_smul _ _ _

theorem coefficientSlotsEquiv_d (xs : List σ) (j : ℕ)
    (f : KoszulSlot xs.length (j+1) → coefficientModule k σ M)
    (t : KoszulSlot xs.length j) :
    coefficientSlotsEquiv k σ M xs j
      (((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j
        ((coefficientSlotsEquiv k σ M xs (j+1)).symm f)) t=
      ∑ s,(koszulSignedVariable k σ M (koszulSlotArrow xs j s t)).hom (f s) := by
  change coefficientSlotOut k σ M xs j t
    (((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j
      (∑ s,coefficientSlotIn k σ M xs (j+1) s (f s)))=_
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact coefficientSlot_d_arrow k σ M xs j s t (f s)
end NSP14.Homological
