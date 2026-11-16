module
public import audit.run17.RequestedGoals
public import NSP14.Additive.Kneser
public import NSP14.Additive.SavchevChen
@[expose] public section
namespace NSP14.Run17
theorem kneser_closed : Requested.Kneser := by
  intro G _ _ _ A B hA hB
  exact Additive.kneser A B hA hB
theorem savchevChen_closed : Requested.SavchevChen := by
  intro u hu ℓ seq hz hl
  exact Additive.savchevChen hu seq hz hl
end NSP14.Run17
