module
public import NSP14.ArithmeticSequence.Source
public import NSP14.Semigroup.IntervalCompletion
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

theorem maxAtom : D.source.maxAtom=D.m+D.v*D.d := by
  apply Nat.le_antisymm
  · change D.source.atoms.max' _≤D.m+D.v*D.d
    apply Finset.max'_le
    intro a ha
    obtain ⟨i,hi,he⟩ := D.atom_eq_generator ((D.source.mem_atoms_iff _).mp ha)
    rw [he]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.d hi) D.m
  · exact D.source.atom_le_maxAtom ((D.source.mem_atoms_iff _).mpr (D.generator_atom D.v le_rfl))

theorem width : D.source.width=D.v*D.d := by
  rw [NSP14.NumericalSemigroup.width,D.maxAtom,D.multiplicity,Nat.add_sub_cancel_left]
end NSP14.ArithmeticSequence.Data
