module
public import NSP14.Homological.KoszulSlotComplete
public import NSP14.Homological.CoefficientKoszulListFunctor
public import NSP14.Homological.KoszulSlotArrow
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

noncomputable def coefficientSlotIn (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    coefficientModule k σ M →ₗ[k] ((coefficientKoszulListFunctor k σ xs).obj M).X j :=
  ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map (koszulSlotIn k σ M xs j s)).hom

noncomputable def coefficientSlotOut (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    ((coefficientKoszulListFunctor k σ xs).obj M).X j →ₗ[k] coefficientModule k σ M :=
  ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map (koszulSlotOut k σ M xs j s)).hom

theorem coefficientSlotOut_ext (xs : List σ) (j : ℕ)
    {a b : ((coefficientKoszulListFunctor k σ xs).obj M).X j}
    (h : ∀ s,coefficientSlotOut k σ M xs j s a=coefficientSlotOut k σ M xs j s b) : a=b := by
  apply sub_eq_zero.mp
  apply koszulSlotOut_zero k σ M xs j
  intro s
  change coefficientSlotOut k σ M xs j s (a-b)=0
  rw [map_sub,h,sub_self]

theorem coefficientSlot_decompose (xs : List σ) (j : ℕ)
    (a : ((coefficientKoszulListFunctor k σ xs).obj M).X j) :
    a=∑ s,coefficientSlotIn k σ M xs j s (coefficientSlotOut k σ M xs j s a) :=
  koszulSlot_decompose k σ M xs j a

theorem coefficientSlot_d_arrow (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (t : KoszulSlot xs.length j) (a : coefficientModule k σ M) :
    coefficientSlotOut k σ M xs j t
      (((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j (coefficientSlotIn k σ M xs (j+1) s a))=
    (koszulSignedVariable k σ M (koszulSlotArrow xs j s t)).hom a := by
  exact congrArg (fun f => f.hom a) (koszulSlot_d_arrow k σ M xs j s t)
end NSP14.Homological
