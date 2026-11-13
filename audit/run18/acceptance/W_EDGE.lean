module
public import audit.run18.RequestedGoals
@[expose] public section
namespace NSP14.Run18.Acceptance
/-- Unclosed original contract; the missing declaration must not be replaced by an assumption. -/
theorem original_W_EDGE : Requested.W_EDGE := NSP14.Run18.edge_closed
end NSP14.Run18.Acceptance
