module
public import audit.run18.RequestedGoals
@[expose] public section
namespace NSP14.Run18.Acceptance
/-- Unclosed original contract; the missing declaration must not be replaced by an assumption. -/
theorem original_W_FIVE : Requested.W_FIVE := NSP14.Run18.five_closed
end NSP14.Run18.Acceptance
