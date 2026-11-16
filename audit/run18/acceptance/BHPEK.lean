module
public import audit.run18.BHPEKClosedGoals
@[expose] public section
namespace NSP14.Run18.Acceptance
/-- Fails until the original arbitrary-characteristic public-input contract is closed. -/
theorem arbitrary_characteristic_bhp_ek : Requested.X_BHP_EK := NSP14.Lex.bhp_ek
end NSP14.Run18.Acceptance
