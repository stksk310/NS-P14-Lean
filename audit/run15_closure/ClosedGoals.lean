module
public import audit.run15_apcone.ClosedGoals
public import NSP14.ArithmeticSequence.BettiFormula
public import NSP14.Target.IntervalAPBetti
@[expose] public section
namespace Run15Closed

/-- The exact originally frozen AP quotient-Betti goal, over every
original field and with the original genuine AP hypotheses unchanged. -/
theorem ap_betti_closed : Run15Remaining.APBettiGoal := by
  intro D k hk i hi
  exact D.semigroup_totalBetti_pos k i hi

/-- A single audit export closes every one of the eight original goals.
No new premise is supplied to any original proposition. -/
theorem all_original_goals_closed :
    Run15Remaining.APBettiGoal ∧ Run15Remaining.APConeBettiGoal ∧
    Run15Remaining.HarmonicGoal ∧ Run15Remaining.RelativeTerminalGoal ∧
    Run15Remaining.ActualTorToRowGoal ∧ Run15Remaining.CorrectedFullTransferGoal ∧
    Run15Remaining.OrdinaryBettiBoundGoal ∧ Run15Remaining.OrdinaryActualCompletionGoal :=
  ⟨ap_betti_closed,Run15APCone.ap_cone_betti_closed,Run15Continuation.harmonic_closed,
   Run15XClosure.relative_terminal_closed,Run15BClosure.actual_tor_to_row_closed,
   Run15FullTransfer.corrected_full_transfer_closed,Run15FullTransfer.ordinary_betti_bound_closed,
   Run15Ordinary.ordinary_actual_completion_closed⟩
end Run15Closed
