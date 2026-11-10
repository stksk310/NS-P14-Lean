module
public import NSP14.Semigroup.IntervalCap
public import NSP14.Semigroup.TerminalResidues
public import NSP14.Semigroup.OffsetVolume
public import NSP14.Semigroup.ActualLayers
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

noncomputable def headIntervalLength (h : S.HeadExponent) : ℕ :=
  if h.val.val ∈ S.aperySet then S.order h.val.val-1 else S.jump (h.val.val-S.multiplicity)-1

theorem head_interval_card (h : S.HeadExponent) :
    ((Finset.range (S.headTopDegree+3)).filter (fun t => S.HeadContributes t h)).card =
      S.headIntervalLength h := by
  have htop := S.head_order_le_top h
  by_cases ha : h.val.val ∈ S.aperySet
  · have he : (Finset.range (S.headTopDegree+3)).filter (fun t => S.HeadContributes t h) =
        Finset.range (S.order h.val.val-1) := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_range,S.headContributes_apery t h ha]
      omega
    rw [he,Finset.card_range,headIntervalLength,ite_eq_left ha]
  · have ht := S.head_sub_terminal (⟨h.property,ha⟩ : S.NonAperyHead h.val.val)
    have hj := S.terminal_jump ht
    have ho : S.order h.val.val = S.order (h.val.val-S.multiplicity)+S.jump (h.val.val-S.multiplicity) := by
      have he : h.val.val-S.multiplicity+S.multiplicity=h.val.val := by
        obtain ⟨x,hx,he⟩ := S.head_predecessor (⟨h.property,ha⟩ : S.NonAperyHead h.val.val)
        omega
      unfold jump
      rw [he]
      have := S.order_add_multiplicity ht.1
      rw [he] at this
      omega
    have he : (Finset.range (S.headTopDegree+3)).filter (fun t => S.HeadContributes t h) =
        Finset.Ico (S.order (h.val.val-S.multiplicity)) (S.order h.val.val-1) := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_range,S.headContributes_nonapery t h ha,Finset.mem_Ico]
      omega
    rw [he,Nat.card_Ico,headIntervalLength,ite_eq_right ha]
    omega

theorem towerResource_sum (k : Type*) [Field k] :
    (∑ t ∈ Finset.range (S.headTopDegree+3), S.towerResource k t) =
      ∑ h : S.HeadExponent, S.headIntervalLength h := by
  simp_rw [S.towerResource_card k,Fintype.card_subtype,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.card_filter,S.head_interval_card]

theorem headIntervalLength_sum :
    (∑ h : S.HeadExponent, S.headIntervalLength h) =
      ∑ r : Fin S.multiplicity, (S.offsetLevel r-1) := by
  have he := S.headExponentEquiv.symm.sum_comp (S.headIntervalLength)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  have ha : (∑ a : S.AperyExponent, S.headIntervalLength (S.headExponentEquiv.symm (Sum.inl a))) =
      ∑ r : Fin S.multiplicity, (S.order (S.apery r)-1) := by
    rw [← S.residueAperyEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro r _
    simp only [headIntervalLength,headExponentEquiv,Equiv.coe_fn_symm_mk,residueAperyEquiv,Equiv.ofBijective_apply]
    rw [ite_eq_left ((S.mem_aperySet_iff _).2 (S.apery_min r))]
  have ht : (∑ a : S.NonAperyHeadExponent, S.headIntervalLength (S.headExponentEquiv.symm (Sum.inr a))) =
      ∑ r : Fin S.multiplicity, (S.offsetLevel r-S.order (S.apery r)) := by
    rw [← S.terminal_excess_sum,← S.terminalHeadExponentEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    change S.headIntervalLength (S.terminalHeadExponentEquiv t).val = _
    rw [headIntervalLength,ite_eq_right (S.terminalHeadExponentEquiv t).property]
    congr 2
    change t.val.val+S.multiplicity-S.multiplicity=t.val.val
    omega
  rw [ha,ht]
  calc
    _ = ∑ r : Fin S.multiplicity, ((S.order (S.apery r)-1)+(S.offsetLevel r-S.order (S.apery r))) := (Finset.sum_add_distrib).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      have h := S.order_apery_le_offsetLevel r
      by_cases hr : r.val=0
      · rw [S.offsetLevel_zero r hr] at h ⊢
        omega
      · have hp := (S.offset_level_bounds r hr).1
        omega

theorem actualLayers_mass_offset (k : Type*) [Field k] :
    (S.actualLayers k).mass S.deficit =
      ∑ r : Fin S.multiplicity, ((S.offsetLevel r-1 : ℕ) : ℚ) := by
  rw [S.actualLayers_mass,← Nat.cast_sum,S.towerResource_sum k,S.headIntervalLength_sum,Nat.cast_sum]

theorem actualLayers_budget (k : Type*) [Field k] :
    (S.actualLayers k).mass S.deficit ≤
      (S.deficit : ℚ)*NSP14.Ordinary.SmallScalar.volume S.embeddingDimension S.deficit := by
  rw [S.actualLayers_mass_offset]
  have he : (∑ r ∈ (Finset.univ : Finset (Fin S.multiplicity)).filter (fun r => r.val ≠ 0),
      ((S.offsetLevel r-1 : ℕ) : ℚ)) = ∑ r : Fin S.multiplicity, ((S.offsetLevel r-1 : ℕ) : ℚ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r _ hn
    have hr : r.val=0 := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
    rw [S.offsetLevel_zero r hr]
    norm_num
  rw [← he]
  exact S.offset_volume_bound
end NSP14.NumericalSemigroup
