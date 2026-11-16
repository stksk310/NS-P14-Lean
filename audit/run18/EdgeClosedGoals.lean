module
public import audit.run18.RequestedGoals
public import NSP14.Width.EdgeAP
public import NSP14.Width.EdgeHoleComparison
@[expose] public section
namespace NSP14.Run18
/-- The original edge contract, including every one-missing alphabet. -/
theorem edge_closed : Requested.W_EDGE := by
  intro S k _ he hw
  dsimp only
  intro hu i
  rcases hu with hu|hu
  · exact S.narrow_fullAP_comparison k he hw hu i
  · exact S.narrow_oneHole_comparison k he hw hu i
end NSP14.Run18
