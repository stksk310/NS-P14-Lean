module
public import NSP14.Homological.WedgeExponent
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable {σ : Type*} [Fintype σ]

theorem koszulWedge_avoid_card (j : ℕ) (v : σ) :
    Fintype.card {F : KoszulWedge σ j // v ∉ F.val}=(Fintype.card σ-1).choose j := by
  let e : {F : KoszulWedge σ j // v ∉ F.val} ≃
      ↥(((Finset.univ : Finset σ).erase v).powersetCard j) :=
    { toFun F := ⟨F.val.val,Finset.mem_powersetCard.mpr ⟨by
        intro x hx
        simp only [Finset.mem_erase,Finset.mem_univ,and_true]
        intro he
        subst x
        exact F.property hx,F.val.property⟩⟩
      invFun F := ⟨⟨F.val,(Finset.mem_powersetCard.mp F.property).2⟩,by
        intro hv
        have h := (Finset.mem_powersetCard.mp F.property).1 hv
        exact (Finset.mem_erase.mp h).1 rfl⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ]

theorem wedge_complement_sum (j : ℕ) (d : σ →₀ ℕ) :
    (∑ F : KoszulWedge σ j,∑ v : σ,if v ∉ F.val then (d v : ℚ) else 0)=
      ((Fintype.card σ-1).choose j : ℚ)*d.degree := by
  rw [Finset.sum_comm]
  have hf (v : σ) : (∑ F : KoszulWedge σ j,if v ∉ F.val then (d v : ℚ) else 0)=
      ((Fintype.card σ-1).choose j : ℚ)*(d v : ℚ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [← Fintype.card_subtype,koszulWedge_avoid_card]
  simp_rw [hf]
  rw [← Finset.mul_sum,← Nat.cast_sum]
  congr 2
  exact (d.sum_fintype (fun _ n => n) (fun _ => rfl)).symm

theorem wedge_harmonic_sum (j : ℕ) (d : σ →₀ ℕ) :
    (∑ F : KoszulWedge σ j,∑ v : σ,
      if v ∉ F.val ∧ 0 < d v then ((d+wedgeExponent F.val) v : ℚ)/((d+wedgeExponent F.val).degree) else 0)=
      ((Fintype.card σ-1).choose j : ℚ)*d.degree/(d.degree+j) := by
  have hf (F : KoszulWedge σ j) (v : σ) :
      (if v ∉ F.val ∧ 0 < d v then ((d+wedgeExponent F.val) v : ℚ)/((d+wedgeExponent F.val).degree) else 0)=
        (if v ∉ F.val then (d v : ℚ) else 0)/(d.degree+j) := by
    by_cases hv : v ∈ F.val
    · simp [hv]
    · have hd : (d+wedgeExponent F.val).degree=d.degree+j := by
        rw [map_add,wedgeExponent_degree,F.property]
      rw [hd]
      by_cases hpos : 0 < d v
      · simp [hv,hpos,wedgeExponent_apply]
      · have hz : d v=0 := Nat.eq_zero_of_not_pos hpos
        simp [hv,hz]
  simp_rw [hf]
  simp_rw [← Finset.sum_div]
  rw [wedge_complement_sum]

universe u
theorem koszulSlot_harmonic_sum (k σ : Type u) [Field k] [Fintype σ] (j : ℕ) (d : σ →₀ ℕ) :
    (∑ s : KoszulSlot (variableList k σ).length j,∑ v : σ,
      if v ∉ koszulSlotWedge (variableList k σ) j s ∧ 0 < d v then
        ((d+wedgeExponent (koszulSlotWedge (variableList k σ) j s)) v : ℚ)/
          (d+wedgeExponent (koszulSlotWedge (variableList k σ) j s)).degree else 0)=
      ((Fintype.card σ-1).choose j : ℚ)*d.degree/(d.degree+j) := by
  calc
    _ = ∑ F : KoszulWedge σ j,∑ v : σ,
        if v ∉ F.val ∧ 0 < d v then ((d+wedgeExponent F.val) v : ℚ)/
          (d+wedgeExponent F.val).degree else 0 :=
      Fintype.sum_equiv (koszulVariableWedgeEquiv k σ j) _ _ (fun _ => rfl)
    _ = _ := wedge_harmonic_sum j d
end NSP14.Homological
