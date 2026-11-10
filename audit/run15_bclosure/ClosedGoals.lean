module
public import audit.run15_xclosure.ClosedGoals
public import NSP14.Ordinary.ActualTorRow
@[expose] public section
namespace Run15BClosure

/-- Exactly the original actual Tor-to-row goal, with its source, field,
relative ring and actual resource row unchanged. -/
theorem actual_tor_to_row_closed : Run15Remaining.ActualTorToRowGoal := by
  intro k hk W j hj
  exact W.actualTor_resource_row j hj
end Run15BClosure
