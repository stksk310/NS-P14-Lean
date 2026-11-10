module
public import NSP14.Homological.KoszulResolution
@[expose] public section
namespace NSP14.Homological
universe u
variable (k σ : Type u) [CommRing k] (M : ModuleCat (VariableRing k σ))

theorem koszulVariableSubmodule_le_iSup (xs : List σ) :
    koszulVariableSubmodule k σ xs M ≤ ⨆ x : σ,(variableOperator k σ M x).range := by
  induction xs with
  | nil => exact bot_le
  | cons x xs ih => exact sup_le (le_iSup (fun y : σ => (variableOperator k σ M y).range) x) ih

theorem variableOperator_range_le (xs : List σ) (x : σ) (hx : x ∈ xs) :
    (variableOperator k σ M x).range ≤ koszulVariableSubmodule k σ xs M := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    rcases List.mem_cons.mp hx with he|he
    · subst x;exact le_sup_left
    · exact (ih he).trans le_sup_right

theorem koszulVariableSubmodule_all [Fintype σ] :
    koszulVariableSubmodule k σ (variableList k σ) M = ⨆ x : σ,(variableOperator k σ M x).range :=
  le_antisymm (koszulVariableSubmodule_le_iSup k σ M _)
    (iSup_le (fun x => variableOperator_range_le k σ M _ x (mem_variableList k σ x)))
end NSP14.Homological
