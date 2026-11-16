module
public import NSP14.Semigroup.IntervalMass
public import NSP14.Semigroup.CutGeneration
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

noncomputable def terminalLinearCount : ℕ :=
  ∑ t : S.TerminalExponent, if S.order t.val.val=1 then 1 else 0

theorem apery_sum_indicator (P : ℕ → Prop) [DecidablePred P] :
    (∑ a : S.AperyExponent, if P a.val.val then 1 else 0) = (S.aperySet.filter P).card := by
  rw [← S.aperyExponentEquivSet.symm.sum_comp]
  change (∑ a : ↥S.aperySet, if P a.val then 1 else 0) = _
  exact (Finset.sum_coe_sort S.aperySet (fun x => if P x then (1:ℕ) else 0)).trans (Finset.card_filter P S.aperySet).symm

theorem towerResource_head_identity (k : Type*) [Field k] :
    S.towerResource k 1 + (S.degreeSet 2).card = S.deficit + S.terminalLinearCount := by
  have hh : S.towerResource k 1 =
      (∑ a : S.AperyExponent, if 3 ≤ S.order a.val.val then 1 else 0) + S.terminalLinearCount := by
    rw [S.towerResource_card k,Fintype.card_subtype,Finset.card_filter]
    rw [← S.headExponentEquiv.symm.sum_comp,Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro a _
      change (if S.HeadContributes 1 ⟨a.val,S.apery_head a.property⟩ then 1 else 0) = _
      rw [S.headContributes_apery 1 _ a.property]
      simp only [show (1:ℕ)+2=3 by decide]
    · rw [← S.terminalHeadExponentEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      change (if S.HeadContributes 1 (S.terminalHeadExponentEquiv a).val then 1 else 0) = _
      rw [S.headContributes_nonapery 1 _ (S.terminalHeadExponentEquiv a).property]
      have hp := S.order_pos a.val.property (S.terminal_pos a.property)
      have hj := S.terminal_jump a.property
      have he : S.order (S.terminalHeadExponentEquiv a).val.val.val = S.order a.val.val+S.jump a.val.val := S.terminal_head_degree_shift a
      have hv : (S.terminalHeadExponentEquiv a).val.val.val-S.multiplicity=a.val.val := by
        change a.val.val+S.multiplicity-S.multiplicity=a.val.val
        omega
      rw [hv,he]
      split_ifs <;> omega
  rw [hh]
  have hd : S.deficit = ∑ a : S.AperyExponent, if 2 ≤ S.order a.val.val then 1 else 0 := by
    have hi := S.apery_sum_indicator (fun x => 2 ≤ S.order x)
    have hc := S.highSet_card
    unfold highSet at hc
    exact (hi.trans hc).symm
  have ha : (S.degreeSet 2).card = ∑ a : S.AperyExponent, if S.order a.val.val=2 then 1 else 0 := by
    unfold degreeSet
    exact (S.apery_sum_indicator (fun x => S.order x=2)).symm
  rw [hd,ha]
  have hs : (∑ a : S.AperyExponent, if 3 ≤ S.order a.val.val then 1 else 0) +
      (∑ a : S.AperyExponent, if S.order a.val.val=2 then 1 else 0) =
      ∑ a : S.AperyExponent, if 2 ≤ S.order a.val.val then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> omega
  omega

theorem terminalLinearCount_le : S.terminalLinearCount ≤ S.embeddingDimension-1 := by
  let T := {t : S.TerminalExponent // S.order t.val.val=1}
  let f : T → ↥(S.atoms.erase S.multiplicity) := fun t =>
    ⟨t.val.val.val,Finset.mem_erase.mpr ⟨by
      intro he
      have ht := t.val.property.2
      rw [he,S.order_multiplicity] at ht
      have ho := S.order_multiple 2
      have he2 : S.multiplicity+S.multiplicity=2*S.multiplicity := by omega
      rw [he2,ho] at ht
      omega,(S.mem_atoms_iff _).2 ((S.order_one_iff_atom t.val.val.property).1 t.property)⟩⟩
  have hi : Function.Injective f := by
    intro a b he
    have hv : a.val.val.val=b.val.val.val := congrArg (fun x : ↥(S.atoms.erase S.multiplicity) => x.val) he
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  have hc := Fintype.card_le_of_injective f hi
  change S.terminalLinearCount ≤ _
  have he : Fintype.card T = S.terminalLinearCount := by
    rw [Fintype.card_subtype,Finset.card_filter]
    rfl
  rw [he,Fintype.card_coe,S.nonmultiplicity_atoms_card] at hc
  exact hc

theorem towerResource_head_cap (k : Type*) [Field k] :
    S.towerResource k 1 + (S.degreeSet 2).card ≤ S.multiplicity-1 := by
  rw [S.towerResource_head_identity k]
  have h := S.terminalLinearCount_le
  have hm := S.multiplicity_eq_embedding_add_deficit
  have he := S.embeddingDimension_pos
  omega
end NSP14.NumericalSemigroup
