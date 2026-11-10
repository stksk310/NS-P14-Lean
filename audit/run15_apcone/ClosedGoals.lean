module
public import audit.run15_ordinary.ClosedGoals
public import NSP14.ArithmeticSequence.ConeBetti
@[expose] public section
namespace Run15APCone

/-- Exactly the frozen original universal goal: arbitrary AP difference,
original coefficient field and every ordinary Tor row. -/
theorem ap_cone_betti_closed : Run15Remaining.APConeBettiGoal := by
  intro D k hk i
  exact D.semigroup_cone_totalBetti k i
end Run15APCone
