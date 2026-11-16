module
public import NSP14.Additive.Sumset
public import NSP14.Additive.Stabilizer
public import NSP14.Additive.ZeroSumSequence
@[expose] public section
open scoped Pointwise
open NSP14.Additive
theorem Run17_iterated_zero (A : Finset (ZMod 6)) : iteratedSum A 0 = {0} := rfl
theorem Run17_iterated_one (A : Finset (ZMod 6)) : iteratedSum A 1 = A :=
  iteratedSum_one A
theorem Run17_independent_choices :
    iteratedSum ({0,1} : Finset (ZMod 6)) 2 = {0,1,2} := by decide
theorem Run17_not_pointwise_double :
    iteratedSum ({0,1} : Finset (ZMod 6)) 2 ≠
      ({0,1} : Finset (ZMod 6)).image (fun x => 2*x) := by decide
theorem Run17_empty_zeroSumFree : ZeroSumFree (fun i : Fin 0 => (i.elim0 : ZMod 6)) :=
  zeroSumFree_empty _
theorem Run17_repeated_positions : ¬ZeroSumFree (fun _ : Fin 3 => (2 : ZMod 6)) := by
  intro h
  have hh := h Finset.univ (by simp)
  exact hh (by decide)
