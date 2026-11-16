module
public import NSP14.Additive.TwoValueSequence
public import NSP14.Additive.SequenceMultiplicity
@[expose] public section
open scoped BigOperators
open NSP14.Additive
namespace Run17Sequences
def seq6 : Fin 4 → ZMod 6 := ![5,5,5,4]
def seq9 : Fin 5 → ZMod 9 := ![2,2,2,4,6]
def boundary6 : Fin 3 → ZMod 6 := ![2,2,3]
def unit6 : (ZMod 6)ˣ := ⟨5,5,by decide,by decide⟩
def unit9 : (ZMod 9)ˣ := ⟨5,2,by decide,by decide⟩
theorem seq6_zeroSumFree : ZeroSumFree seq6 := by decide
theorem seq9_zeroSumFree : ZeroSumFree seq9 := by decide
theorem seq6_sum : representativeSum unit6 seq6 = 5 := by decide
theorem seq9_sum : representativeSum unit9 seq9 = 8 := by decide
theorem seq6_long : 6 < 2*4 := by decide
theorem seq9_long : 9 < 2*5 := by decide
theorem boundary_zeroSumFree : ZeroSumFree boundary6 := by decide
theorem boundary_unit_sums : ∀ c : (ZMod 6)ˣ,
    representativeSum c boundary6 = 7 ∨ representativeSum c boundary6 = 11 := by decide
theorem strict_boundary_required : ¬∃ c : (ZMod 6)ˣ,
    representativeSum c boundary6 < 6 := by decide
theorem mod2_single : ZeroSumFree (fun _ : Fin 1 => (1 : ZMod 2)) := by decide
theorem mod3_double : ZeroSumFree (fun _ : Fin 2 => (1 : ZMod 3)) := by decide
theorem mod1_nonempty_impossible : ¬ZeroSumFree (fun _ : Fin 1 => (0 : ZMod 1)) := by decide
theorem seq9_general_export : ∃ c : (ZMod 9)ˣ, representativeSum c seq9 < 9 :=
  savchevChen (by decide) seq9 seq9_zeroSumFree seq9_long
theorem repeat_units (u : ℕ) [NeZero u] (a : (ZMod u)ˣ) :
    ZeroSumFree (fun _ : Fin (u-1) => (a : ZMod u)) := zeroSumFree_repeat_unit u a
theorem seq9_multiplicities : MultisetZeroSumFree (occurrenceMultiset seq9) :=
  (zeroSumFree_multiset_iff seq9).mp seq9_zeroSumFree
theorem seq9_list : ListZeroSumFree (List.ofFn seq9) :=
  (zeroSumFree_ofFn_iff seq9).mpr seq9_zeroSumFree
end Run17Sequences
