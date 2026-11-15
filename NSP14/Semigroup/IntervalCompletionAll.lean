module
public import NSP14.Semigroup.IntervalCompletion
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

/-- The generated interval contains the original semigroup, including e=1. -/
theorem le_literal_interval : S.carrier ≤ AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) := by
  rw [←S.closure_atoms]
  apply AddSubmonoid.closure_mono
  intro n hn
  have ha := (S.mem_atoms_iff n).mp hn
  exact ⟨S.multiplicity_le ha.1 ha.2.1,S.atom_le_maxAtom hn⟩

/-- Unconditional literal completion. Its cofinite witness comes from S. -/
noncomputable def intervalCompletionAll : NumericalSemigroup where
  carrier := AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom)
  conductor := S.conductor
  cofinite := fun n hn => S.le_literal_interval (S.cofinite n hn)

@[simp] theorem intervalCompletionAll_carrier : S.intervalCompletionAll.carrier=
    AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) := rfl

theorem intervalCompletionAll_carrier_eq (he : 2 ≤ S.embeddingDimension) :
    S.intervalCompletionAll.carrier=(S.intervalCompletion he).carrier :=
  (S.intervalCompletion_carrier he).symm
end NSP14.NumericalSemigroup
