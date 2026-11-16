module
public import NSP14.Homological.KoszulArrowWedge
@[expose] public section
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

theorem koszulSlot_delete_partner (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (v : σ)
    (hv : v ∈ koszulSlotWedge (variableList k σ) (j+1) s) :
    ∃ (t : KoszulSlot (variableList k σ).length j) (b : Bool),
      koszulSlotWedge (variableList k σ) j t=(koszulSlotWedge (variableList k σ) (j+1) s).erase v ∧
      koszulSlotArrow (variableList k σ) j s t=some (v,b) := by
  let F : KoszulWedge σ j :=
    ⟨(koszulSlotWedge (variableList k σ) (j+1) s).erase v,by
      rw [Finset.card_erase_of_mem hv,koszulSlotWedge_card _ (variableList_nodup k σ)]
      omega⟩
  let t := (koszulVariableWedgeEquiv k σ j).symm F
  have ht : koszulSlotWedge (variableList k σ) j t=(koszulSlotWedge (variableList k σ) (j+1) s).erase v :=
    congrArg Subtype.val ((koszulVariableWedgeEquiv k σ j).apply_symm_apply F)
  have hn : v ∉ koszulSlotWedge (variableList k σ) j t := by rw [ht];exact Finset.notMem_erase _ _
  obtain ⟨p,b,hw,ha⟩ := koszulSlot_insert_partner (variableList k σ) j t v (mem_variableList k σ v) hn
  have he : p=s := by
    apply koszulSlotWedge_injective _ (variableList_nodup k σ) (j+1)
    rw [hw,ht,Finset.insert_erase hv]
  subst p
  exact ⟨t,b,ht,ha⟩

noncomputable def koszulSlotSelectedVariable (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) : σ :=
  Classical.choose (Finset.card_pos.mp (by rw [koszulSlotWedge_card _ (variableList_nodup k σ)];omega :
    0 < (koszulSlotWedge (variableList k σ) (j+1) s).card))

omit [Field k] in
theorem koszulSlotSelectedVariable_mem (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    koszulSlotSelectedVariable k σ j s ∈ koszulSlotWedge (variableList k σ) (j+1) s :=
  Classical.choose_spec (Finset.card_pos.mp (by rw [koszulSlotWedge_card _ (variableList_nodup k σ)];omega :
    0 < (koszulSlotWedge (variableList k σ) (j+1) s).card))
end NSP14.Homological
