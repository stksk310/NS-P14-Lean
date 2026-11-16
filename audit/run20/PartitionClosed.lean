module
public import audit.run20.RequestedGoals
@[expose] public section
namespace NSP14.Run20
theorem partition_closed : Requested.I_PARTITION := by
  intro S
  exact ⟨S.parameter_partition,S.cut_parameters,S.narrow_parameters⟩
end NSP14.Run20
