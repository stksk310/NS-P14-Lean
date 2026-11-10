module
public import NSP14.Homological.KoszulStandardMinor
public import NSP14.Homological.WeightedPivot
public import NSP14.Homological.WedgeCounting
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] [Nonempty σ]
  (M : ModuleCat.{u} (VariableRing k σ)) (m : MonomialOrder σ)
  {q : ℕ} (g : Fin q → coefficientModule k σ M)
  (hg : Submodule.span (VariableRing k σ) (Set.range g)=⊤)
  [Fintype (ModuleStandard k m g)] [Module.Finite k (coefficientModule k σ M)]

omit [Nonempty σ] [Fintype (ModuleStandard k m g)] [Module.Finite k (coefficientModule k σ M)] in
theorem standardKoszulTerm_degree (j : ℕ) (a : StandardKoszulTarget k σ M m g j) :
    (moduleTermExponent m (standardKoszulTerm k σ M m g a)).degree=
      (moduleTermExponent m a.1.val).degree+j := by
  rw [standardKoszulTerm,moduleTermExponent_shift,map_add,wedgeExponent_degree,
    koszulSlotWedge_card _ (variableList_nodup k σ)]

include hg in
/-- Rational weighted matching, evaluated in the actual Koszul differential.
Neither the fractions nor the averaging are performed in k. -/
theorem standardKoszul_weighted_rank (j : ℕ) (hj : 0 < j) :
    (∑ a : StandardKoszulTarget k σ M m g j,∑ v : σ,
      if v ∉ koszulSlotWedge (variableList k σ) j a.2 ∧ 0 < moduleTermExponent m a.1.val v then
        (moduleTermExponent m (standardKoszulTerm k σ M m g a) v : ℚ)/
          (moduleTermExponent m (standardKoszulTerm k σ M m g a)).degree else 0) ≤
      (koszulBoundaryRank k σ M (j+1) : ℚ) := by
  let aug : (StandardKoszulTarget k σ M m g j) → ModuleTerm m (q:=q) := fun i => standardKoszulTerm k σ M m g (j:=j) i
  let T : Finset (ModuleTerm m (q:=q)) := (Finset.univ : Finset (StandardKoszulTarget k σ M m g j)).image aug
  let a : (StandardKoszulTarget k σ M m g j) → ↥T := fun i => ⟨aug i,Finset.mem_image_of_mem aug (Finset.mem_univ i)⟩
  let E : (StandardKoszulTarget k σ M m g j) → σ → Prop := fun i v =>
    v ∉ koszulSlotWedge (variableList k σ) j i.2 ∧ 0 < moduleTermExponent m i.1.val v
  let w : ↥T → σ → ℚ := fun α v =>
    (moduleTermExponent m α.val v : ℚ)/(moduleTermExponent m α.val).degree
  have hpos (α : ↥T) : 0 < (moduleTermExponent m α.val).degree := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp α.property
    rw [← hi,standardKoszulTerm_degree]
    omega
  have hw (α : ↥T) (v : σ) : 0 ≤ w α v := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hs (α : ↥T) : ∑ v,w α v=1 := by
    change (∑ v : σ,(moduleTermExponent m α.val v : ℚ)/(moduleTermExponent m α.val).degree)=1
    rw [← Finset.sum_div,← Nat.cast_sum]
    have he : ∑ v : σ,moduleTermExponent m α.val v=(moduleTermExponent m α.val).degree :=
      ((moduleTermExponent m α.val).sum_fintype (fun _ n => n) (fun _ => rfl)).symm
    rw [he,div_self (Nat.cast_ne_zero.mpr (ne_of_gt (hpos α)))]
  have hb := weighted_pivot_bound a E w hw hs
  let p : ModuleTerm m (q:=q) → σ := fun z =>
    if hz : z ∈ T then maximizingPivot a E ⟨z,hz⟩ else Classical.arbitrary σ
  have hp (i : (StandardKoszulTarget k σ M m g j)) : p (aug i)=maximizingPivot a E (a i) := by
    simp only [p,dite_eq_left (show aug i ∈ T from Finset.mem_image_of_mem aug (Finset.mem_univ i))]
    rfl
  let e : {i : (StandardKoszulTarget k σ M m g j) // E i (maximizingPivot a E (a i))} ≃ PivotKoszulTarget k σ M m g j p :=
    { toFun i := ⟨i.val,by change E i.val (p (aug i.val));rw [hp];exact i.property⟩
      invFun i := ⟨i.val,by rw [← hp];exact i.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hc := pivotKoszulTarget_rank k σ M m g (j:=j) p hg
  rw [Nat.card_congr e] at hb
  simpa only [E,w,a,aug] using hb.trans (Nat.cast_le.mpr hc)

include hg in
theorem standardKoszul_boundary_lower (j : ℕ) (hj : 0 < j) :
    ((Fintype.card σ-1).choose j : ℚ)*
      (∑ i : ModuleStandard k m g,(moduleTermExponent m i.val).degree/
        ((moduleTermExponent m i.val).degree+j : ℚ)) ≤
      (koszulBoundaryRank k σ M (j+1) : ℚ) := by
  have h := standardKoszul_weighted_rank k σ M m g hg j hj
  have hf (i : ModuleStandard k m g) :
      (∑ s : KoszulSlot (variableList k σ).length j,∑ v : σ,
        if v ∉ koszulSlotWedge (variableList k σ) j s ∧ 0 < moduleTermExponent m i.val v then
          (moduleTermExponent m (standardKoszulTerm k σ M m g (i,s)) v : ℚ)/
            (moduleTermExponent m (standardKoszulTerm k σ M m g (i,s))).degree else 0)=
        ((Fintype.card σ-1).choose j : ℚ)*(moduleTermExponent m i.val).degree/
          ((moduleTermExponent m i.val).degree+j) := by
    simpa only [standardKoszulTerm,moduleTermExponent_shift] using
      koszulSlot_harmonic_sum k σ j (moduleTermExponent m i.val)
  change (∑ a : ModuleStandard k m g × KoszulSlot (variableList k σ).length j,_) ≤ _ at h
  rw [Fintype.sum_prod_type] at h
  simp_rw [hf,mul_div_assoc] at h
  rw [← Finset.mul_sum] at h
  exact h
end NSP14.Homological
