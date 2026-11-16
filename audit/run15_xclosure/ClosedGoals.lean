module
public import audit.run15_continuation.ClosedGoals
@[expose] public section
namespace Run15XClosure

/-- The exact original r+1 terminal goal. No finite-P or finite-k
hypothesis about G, and no vanishing input, is added. -/
theorem relative_terminal_closed : Run15Remaining.RelativeTerminalGoal := by
  intro k hk W
  exact W.relative_Euler_terminal
end Run15XClosure
