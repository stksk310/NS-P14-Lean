module
public import audit.run20.PartitionClosed
public import NSP14.Main
@[expose] public section
namespace NSP14.Run20
theorem main_closed : Requested.I_MAIN := NumericalSemigroup.p14_totalBetti_le_intervalCompletion
theorem all_closed : Requested.I_PARTITION ∧ Requested.I_MAIN := ⟨partition_closed,main_closed⟩
end NSP14.Run20
