module
public import audit.run18.RequestedGoals
public import NSP14.Width.SparseComparison
@[expose] public section
namespace NSP14.Run18
/-- Exactly one assigned ID is closed here; the other five are not asserted. -/
theorem sparse_closed : Requested.W_SPARSE := by
  intro S k _ he hw
  dsimp only
  intro hu i
  exact S.narrow_sparse_comparison k he hw hu i
end NSP14.Run18
