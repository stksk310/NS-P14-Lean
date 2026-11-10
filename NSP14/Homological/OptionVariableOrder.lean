module
public import NSP14.Homological.KoszulResolution
@[expose] public section
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Fintype σ]
noncomputable def fullOptionOrder : List (Option σ) := none::(variableList k σ).map some

theorem fullOptionOrder_all (a : Option σ) : a∈fullOptionOrder k σ := by
  cases a with
  | none => exact List.mem_cons_self
  | some a => exact List.mem_cons_of_mem none (List.mem_map.mpr ⟨a,mem_variableList k σ a,rfl⟩)

theorem fullOptionOrder_nodup : (fullOptionOrder k σ).Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨by simp,(variableList_nodup k σ).map (Option.some_injective _)⟩
end NSP14.Homological
