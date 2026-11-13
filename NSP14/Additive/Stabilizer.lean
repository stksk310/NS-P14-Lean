module
public import NSP14.Additive.Sumset
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
@[expose] public section
open scoped Pointwise
open scoped Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
/-- The actual translation stabilizer, with its additive subgroup structure. -/
def sumStabilizer (S : Finset G) : AddSubgroup G := AddAction.stabilizer G (S : Set G)
@[simp] theorem mem_sumStabilizer (S : Finset G) (g : G) :
    g ∈ sumStabilizer S ↔ g +ᵥ S = S := by
  rw [sumStabilizer,AddAction.stabilizer_coe_finset]
  rfl
theorem sumStabilizer_eq_action (S : Finset G) :
    sumStabilizer S = AddAction.stabilizer G S := AddAction.stabilizer_coe_finset S
variable [Fintype G]
/-- Saturation by all elements of the specified subgroup. -/
noncomputable def thicken (A : Finset G) (H : AddSubgroup G) : Finset G :=
  A + (H : Set G).toFinset
end NSP14.Additive
