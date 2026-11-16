module
public import audit.run15.RemainingGoals
@[expose] public section
namespace Run15Continuation

/-- This is the exact originally declared goal, without additional rank,
presentation, standard-basis, or characteristic hypotheses. -/
theorem harmonic_closed : Run15Remaining.HarmonicGoal := by
  intro k hk r M hP hK G b N hgen hN j hj
  exact NSP14.Homological.harmonic_bound k r M G b N hgen hN j hj

end Run15Continuation
