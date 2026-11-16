module
public import NSP14.Homological.TwoStepSlots
public import NSP14.Homological.FactorRange
public import NSP14.Homological.KoszulMomentRank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped BigOperators Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ)) (d n : ℕ)
  (e : coefficientModule k σ M ≃ₗ[k] ((Fin d → k) × (Fin n → k))) (points : σ → k)
  (hact : ∀ v (a : coefficientModule k σ M),
    e ((MvPolynomial.X v : VariableRing k σ) • a)=
      (0,momentFunctional k d (points v) (e a).1 • (fun i : Fin n => points v^i.val)))

include hact in
theorem twoStepSignedEntry (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1))
    (t : KoszulSlot (variableList k σ).length j) (a : coefficientModule k σ M) :
    e ((koszulSignedVariable k σ M (koszulSlotArrow (variableList k σ) j s t)).hom a)=
      (0,koszulMomentFunctional k σ points d j s t (e a).1 • koszulMomentImage k σ points n j s t) := by
  cases ha : koszulSlotArrow (variableList k σ) j s t with
  | none =>
    simp only [koszulSignedVariable,koszulMomentFunctional,koszulMomentImage,ha,ModuleCat.hom_zero,LinearMap.zero_apply,map_zero,zero_smul]
    rfl
  | some p =>
    rcases p with ⟨v,b⟩
    cases b with
    | false =>
      change e ((MvPolynomial.X v : VariableRing k σ) • a)=_
      rw [hact]
      simp [koszulMomentFunctional,koszulMomentImage,ha]
    | true =>
      change e (-((MvPolynomial.X v : VariableRing k σ) • a))=_
      rw [map_neg,hact]
      simp [koszulMomentFunctional,koszulMomentImage,ha,neg_smul]

include hact in
theorem twoStepBoundary_factor (j : ℕ) :
    (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom=
      (twoStepUpperInclusion k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j).comp
        ((koszulMomentMap k σ points d n j).comp
          (twoStepLowerProjection k σ M (Fin d → k) (Fin n → k) e (variableList k σ) (j+1))) := by
  apply LinearMap.ext
  intro a
  apply (twoStepSlotsEquiv k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j).injective
  change twoStepSlotsEquiv k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j
    (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j a)=
    twoStepSlotsEquiv k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j
      (twoStepUpperInclusion k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j
        (koszulMomentMap k σ points d n j
          (twoStepLowerProjection k σ M (Fin d → k) (Fin n → k) e (variableList k σ) (j+1) a)))
  rw [twoStepSlotsEquiv_upper]
  apply Prod.ext
  · funext t
    change (e (coefficientSlotsEquiv k σ M (variableList k σ) j
      ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom a) t)).1=0
    have he := coefficientSlotsEquiv_d k σ M (variableList k σ) j
      (coefficientSlotsEquiv k σ M (variableList k σ) (j+1) a) t
    rw [LinearEquiv.symm_apply_apply] at he
    rw [he,map_sum]
    change (∑ s,e ((koszulSignedVariable k σ M (koszulSlotArrow (variableList k σ) j s t)).hom
      (coefficientSlotsEquiv k σ M (variableList k σ) (j+1) a s))).1=0
    simp only [twoStepSignedEntry k σ M d n e points hact]
    rw [finiteSum_fst]
    simp only [Finset.sum_const_zero]
  · funext t
    change (e (coefficientSlotsEquiv k σ M (variableList k σ) j
      ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom a) t)).2=_
    have he := coefficientSlotsEquiv_d k σ M (variableList k σ) j
      (coefficientSlotsEquiv k σ M (variableList k σ) (j+1) a) t
    rw [LinearEquiv.symm_apply_apply] at he
    rw [he,map_sum]
    simp only [twoStepSignedEntry k σ M d n e points hact]
    rw [finiteSum_snd]
    change (∑ s,koszulMomentFunctional k σ points d j s t
        (e (coefficientSlotsEquiv k σ M (variableList k σ) (j+1) a s)).1 •
          koszulMomentImage k σ points n j s t)=_
    symm
    unfold koszulMomentMap
    rw [rankOneIncidence_apply]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : koszulIncidenceActive k σ j s t
    · rw [ite_eq_left h]
      rfl
    · rw [ite_eq_right h]
      have ha : koszulSlotArrow (variableList k σ) j s t=none := by
        cases ha : koszulSlotArrow (variableList k σ) j s t with
        | none => rfl
        | some p => simp [koszulIncidenceActive,ha] at h
      simp only [koszulMomentFunctional,ha,LinearMap.zero_apply,zero_smul]

include hact in
theorem twoStepBoundary_range_finrank (j : ℕ) :
    Module.finrank k ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom.range)=
      Module.finrank k (koszulMomentMap k σ points d n j).range :=
  factorization_range_finrank k _ _ _ _
    (twoStepLowerProjection_surjective k σ M (Fin d → k) (Fin n → k) e (variableList k σ) (j+1))
    (twoStepUpperInclusion_injective k σ M (Fin d → k) (Fin n → k) e (variableList k σ) j)
    (twoStepBoundary_factor k σ M d n e points hact j)

include hact in
theorem twoStepBoundary_rank_above (hp : Function.Injective points) (j : ℕ)
    (hrow : Fintype.card σ-j ≤ n) (hcol : d ≤ j+1) :
    Module.finrank k ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom.range)=
      d*(Fintype.card σ).choose (j+1) := by
  rw [twoStepBoundary_range_finrank k σ M d n e points hact]
  rw [LinearMap.finrank_range_of_inj (koszulMomentMap_injective k σ points hp d n j hrow hcol)]
  rw [Module.finrank_pi_fintype]
  simp [koszulSlot_card,variableList_length,Nat.mul_comm]

include hact in
theorem twoStepBoundary_rank_below (hp : Function.Injective points) (j : ℕ)
    (hrow : n ≤ Fintype.card σ-j) (hcol : j+1 ≤ d) :
    Module.finrank k ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom.range)=
      n*(Fintype.card σ).choose j := by
  rw [twoStepBoundary_range_finrank k σ M d n e points hact,
    LinearMap.range_eq_top.mpr (koszulMomentMap_surjective k σ points hp d n j hrow hcol),finrank_top]
  rw [Module.finrank_pi_fintype]
  simp [koszulSlot_card,variableList_length,Nat.mul_comm]
end NSP14.Homological
