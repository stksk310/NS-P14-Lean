module
public import audit.run15_fulltransfer.ClosedGoals
public import NSP14.Ordinary.Closure
@[expose] public section
namespace Run15Ordinary

/-- Exactly the original actual completed-cone comparison, over the
original arbitrary field, all rows, and each ring's own minimal variables. -/
theorem ordinary_actual_completion_closed : Run15Remaining.OrdinaryActualCompletionGoal := by
  intro S k hk he
  exact NSP14.Ordinary.ordinary_actual_completion_betti_le S k he
end Run15Ordinary
