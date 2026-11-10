module
public import NSP14
@[expose] public section
namespace KoszulSlotsAcceptance
open NSP14.Homological
theorem actual_slot_count (r j : ℕ) : Fintype.card (KoszulSlot r j)=r.choose j :=
  koszulSlot_card r j
end KoszulSlotsAcceptance
