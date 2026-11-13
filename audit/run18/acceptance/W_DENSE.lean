module
public import audit.run18.RequestedGoals
@[expose] public section
namespace NSP14.Run18.Acceptance
/-- Unclosed original contract; the missing declaration must not be replaced by an assumption. -/
theorem original_W_DENSE : Requested.W_DENSE := NSP14.Run18.dense_closed
end NSP14.Run18.Acceptance
