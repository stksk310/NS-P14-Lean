module
public import audit.run15_h0closure.ClosedGoals
public import NSP14.Ordinary.NumericalBettiClosure
@[expose] public section
namespace Run15FullTransfer

/-- Exactly the original full e-variable, H0-corrected comparison. -/
theorem corrected_full_transfer_closed : Run15Remaining.CorrectedFullTransferGoal := by
  intro k hk W i
  exact W.correctedFullTransfer i

/-- Exactly the original arbitrary-field, all-positive-row source bound.
The proved theorem is stronger: the numerical capacity does not require width. -/
theorem ordinary_betti_bound_closed : Run15Remaining.OrdinaryBettiBoundGoal := by
  intro S k hk he _ i hi
  exact NSP14.Ordinary.ordinary_betti_bound S k he i hi
end Run15FullTransfer
