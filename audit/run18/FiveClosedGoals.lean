module
public import audit.run18.RequestedGoals
public import NSP14.Width.FiveComparison
@[expose] public section
namespace NSP14.Run18
/-- The frozen W_FIVE contract, without extra source or field assumptions. -/
theorem five_closed : Requested.W_FIVE := by
  intro S k _ he hw i
  exact S.narrow_five_comparison k he hw i
end NSP14.Run18
