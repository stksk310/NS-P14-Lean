module
public import audit.run18.RequestedGoals
public import NSP14.Width.DenseResources
@[expose] public section
namespace NSP14.Run18
/-- The resource conjunct is closed without weakening its frozen contract.
The DenseClosure conjunct and the W_DENSE assigned ID remain open. -/
theorem dense_resources_closed : Requested.DenseResources := by
  intro D k _ t _ hu ht
  exact D.dense_resources k t hu ht
end NSP14.Run18
